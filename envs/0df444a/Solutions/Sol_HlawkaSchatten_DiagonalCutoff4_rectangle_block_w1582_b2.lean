-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:43.765986+00:00
-- url     : https://prove2.me/submissions/7fd23d48-8159-44a7-a0fb-a546e3fad554

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
theorem support_rectangle_w1582_s6_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-27646113/156250000 : ℝ)*x 0 + (1084853583/2000000000 : ℝ)*x 1 + (2610227401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27646113/156250000 : ℝ)^4661 ≤ (217302912389/2000000000000 : ℝ)^3637 := by
    have hnat : (27646113 : ℕ)^4661*2000000000000^3637 ≤ 217302912389^3637*156250000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27646113 156250000 217302912389 2000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084853583/2000000000 : ℝ)^4661 ≤ (45660922791393/100000000000000 : ℝ)^3637 := by
    have hnat : (1084853583 : ℕ)^4661*100000000000000^3637 ≤ 45660922791393^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084853583 2000000000 45660922791393 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610227401/5000000000 : ℝ)^4661 ≤ (43473931577021/100000000000000 : ℝ)^3637 := by
    have hnat : (2610227401 : ℕ)^4661*100000000000000^3637 ≤ 43473931577021^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610227401 5000000000 43473931577021 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27646113/156250000 : ℝ), (1084853583/2000000000 : ℝ), (2610227401/5000000000 : ℝ)] ![(217302912389/2000000000000 : ℝ), (45660922791393/100000000000000 : ℝ), (43473931577021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27646113/156250000 : ℝ)|^4661 ≤ (217302912389/2000000000000 : ℝ)^3637
        have hw : |(-27646113/156250000 : ℝ)|=(27646113/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084853583/2000000000 : ℝ)|^4661 ≤ (45660922791393/100000000000000 : ℝ)^3637
        have hw : |(1084853583/2000000000 : ℝ)|=(1084853583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610227401/5000000000 : ℝ)|^4661 ≤ (43473931577021/100000000000000 : ℝ)^3637
        have hw : |(2610227401/5000000000 : ℝ)|=(2610227401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s6_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334215399/625000000 : ℝ)*x 0 + (-1873596573/10000000000 : ℝ)*x 1 + (5220454911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334215399/625000000 : ℝ)^4661 ≤ (22416916541433/50000000000000 : ℝ)^3637 := by
    have hnat : (334215399 : ℕ)^4661*50000000000000^3637 ≤ 22416916541433^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334215399 625000000 22416916541433 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873596573/10000000000 : ℝ)^4661 ≤ (11692234168377/100000000000000 : ℝ)^3637 := by
    have hnat : (1873596573 : ℕ)^4661*100000000000000^3637 ≤ 11692234168377^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873596573 10000000000 11692234168377 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220454911/10000000000 : ℝ)^4661 ≤ (21736966370149/50000000000000 : ℝ)^3637 := by
    have hnat : (5220454911 : ℕ)^4661*50000000000000^3637 ≤ 21736966370149^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220454911 10000000000 21736966370149 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334215399/625000000 : ℝ), (-1873596573/10000000000 : ℝ), (5220454911/10000000000 : ℝ)] ![(22416916541433/50000000000000 : ℝ), (11692234168377/100000000000000 : ℝ), (21736966370149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334215399/625000000 : ℝ)|^4661 ≤ (22416916541433/50000000000000 : ℝ)^3637
        have hw : |(334215399/625000000 : ℝ)|=(334215399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1873596573/10000000000 : ℝ)|^4661 ≤ (11692234168377/100000000000000 : ℝ)^3637
        have hw : |(-1873596573/10000000000 : ℝ)|=(1873596573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220454911/10000000000 : ℝ)|^4661 ≤ (21736966370149/50000000000000 : ℝ)^3637
        have hw : |(5220454911/10000000000 : ℝ)|=(5220454911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s6_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069489279/2000000000 : ℝ)*x 0 + (5220454891/10000000000 : ℝ)*x 1 + (-234199573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069489279/2000000000 : ℝ)^4661 ≤ (22416916600529/50000000000000 : ℝ)^3637 := by
    have hnat : (1069489279 : ℕ)^4661*50000000000000^3637 ≤ 22416916600529^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069489279 2000000000 22416916600529 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220454891/10000000000 : ℝ)^4661 ≤ (43473932526853/100000000000000 : ℝ)^3637 := by
    have hnat : (5220454891 : ℕ)^4661*100000000000000^3637 ≤ 43473932526853^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220454891 10000000000 43473932526853 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234199573/1250000000 : ℝ)^4661 ≤ (233844685127/2000000000000 : ℝ)^3637 := by
    have hnat : (234199573 : ℕ)^4661*2000000000000^3637 ≤ 233844685127^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234199573 1250000000 233844685127 2000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069489279/2000000000 : ℝ), (5220454891/10000000000 : ℝ), (-234199573/1250000000 : ℝ)] ![(22416916600529/50000000000000 : ℝ), (43473932526853/100000000000000 : ℝ), (233844685127/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069489279/2000000000 : ℝ)|^4661 ≤ (22416916600529/50000000000000 : ℝ)^3637
        have hw : |(1069489279/2000000000 : ℝ)|=(1069489279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220454891/10000000000 : ℝ)|^4661 ≤ (43473932526853/100000000000000 : ℝ)^3637
        have hw : |(5220454891/10000000000 : ℝ)|=(5220454891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234199573/1250000000 : ℝ)|^4661 ≤ (233844685127/2000000000000 : ℝ)^3637
        have hw : |(-234199573/1250000000 : ℝ)|=(234199573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s6_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423825153/1000000000 : ℝ)*x 0 + (2000647031/5000000000 : ℝ)*x 1 + (4486342213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423825153/1000000000 : ℝ)^4661 ≤ (33282878450323/100000000000000 : ℝ)^3637 := by
    have hnat : (423825153 : ℕ)^4661*100000000000000^3637 ≤ 33282878450323^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423825153 1000000000 33282878450323 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000647031/5000000000 : ℝ)^4661 ≤ (30917169146333/100000000000000 : ℝ)^3637 := by
    have hnat : (2000647031 : ℕ)^4661*100000000000000^3637 ≤ 30917169146333^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000647031 5000000000 30917169146333 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486342213/10000000000 : ℝ)^4661 ≤ (4474994047997/12500000000000 : ℝ)^3637 := by
    have hnat : (4486342213 : ℕ)^4661*12500000000000^3637 ≤ 4474994047997^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486342213 10000000000 4474994047997 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423825153/1000000000 : ℝ), (2000647031/5000000000 : ℝ), (4486342213/10000000000 : ℝ)] ![(33282878450323/100000000000000 : ℝ), (30917169146333/100000000000000 : ℝ), (4474994047997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423825153/1000000000 : ℝ)|^4661 ≤ (33282878450323/100000000000000 : ℝ)^3637
        have hw : |(423825153/1000000000 : ℝ)|=(423825153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000647031/5000000000 : ℝ)|^4661 ≤ (30917169146333/100000000000000 : ℝ)^3637
        have hw : |(2000647031/5000000000 : ℝ)|=(2000647031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486342213/10000000000 : ℝ)|^4661 ≤ (4474994047997/12500000000000 : ℝ)^3637
        have hw : |(4486342213/10000000000 : ℝ)|=(4486342213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s6_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769377559/10000000000 : ℝ)*x 0 + (1305379829/2500000000 : ℝ)*x 1 + (5423195553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769377559/10000000000 : ℝ)^4661 ≤ (5432676402529/50000000000000 : ℝ)^3637 := by
    have hnat : (1769377559 : ℕ)^4661*50000000000000^3637 ≤ 5432676402529^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769377559 10000000000 5432676402529 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305379829/2500000000 : ℝ)^4661 ≤ (43485292672843/100000000000000 : ℝ)^3637 := by
    have hnat : (1305379829 : ℕ)^4661*100000000000000^3637 ≤ 43485292672843^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305379829 2500000000 43485292672843 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423195553/10000000000 : ℝ)^4661 ≤ (356635582143/781250000000 : ℝ)^3637 := by
    have hnat : (5423195553 : ℕ)^4661*781250000000^3637 ≤ 356635582143^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423195553 10000000000 356635582143 781250000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769377559/10000000000 : ℝ), (1305379829/2500000000 : ℝ), (5423195553/10000000000 : ℝ)] ![(5432676402529/50000000000000 : ℝ), (43485292672843/100000000000000 : ℝ), (356635582143/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769377559/10000000000 : ℝ)|^4661 ≤ (5432676402529/50000000000000 : ℝ)^3637
        have hw : |(-1769377559/10000000000 : ℝ)|=(1769377559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305379829/2500000000 : ℝ)|^4661 ≤ (43485292672843/100000000000000 : ℝ)^3637
        have hw : |(1305379829/2500000000 : ℝ)|=(1305379829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423195553/10000000000 : ℝ)|^4661 ≤ (356635582143/781250000000 : ℝ)^3637
        have hw : |(5423195553/10000000000 : ℝ)|=(5423195553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s6_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119157241/5000000000 : ℝ)*x 0 + (896761873/2000000000 : ℝ)*x 1 + (2001922709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119157241/5000000000 : ℝ)^4661 ≤ (33283511999591/100000000000000 : ℝ)^3637 := by
    have hnat : (2119157241 : ℕ)^4661*100000000000000^3637 ≤ 33283511999591^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119157241 5000000000 33283511999591 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896761873/2000000000 : ℝ)^4661 ≤ (35774052342581/100000000000000 : ℝ)^3637 := by
    have hnat : (896761873 : ℕ)^4661*100000000000000^3637 ≤ 35774052342581^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896761873 2000000000 35774052342581 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001922709/5000000000 : ℝ)^4661 ≤ (7735608911663/25000000000000 : ℝ)^3637 := by
    have hnat : (2001922709 : ℕ)^4661*25000000000000^3637 ≤ 7735608911663^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001922709 5000000000 7735608911663 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119157241/5000000000 : ℝ), (896761873/2000000000 : ℝ), (2001922709/5000000000 : ℝ)] ![(33283511999591/100000000000000 : ℝ), (35774052342581/100000000000000 : ℝ), (7735608911663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119157241/5000000000 : ℝ)|^4661 ≤ (33283511999591/100000000000000 : ℝ)^3637
        have hw : |(2119157241/5000000000 : ℝ)|=(2119157241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896761873/2000000000 : ℝ)|^4661 ≤ (35774052342581/100000000000000 : ℝ)^3637
        have hw : |(896761873/2000000000 : ℝ)|=(896761873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2001922709/5000000000 : ℝ)|^4661 ≤ (7735608911663/25000000000000 : ℝ)^3637
        have hw : |(2001922709/5000000000 : ℝ)|=(2001922709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11159/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (2321940186287819/50000000000000000000 : ℝ) := by
    have hpowers : (11159/100000 : ℝ)^4659 ≤ (2321940186287819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11159 : ℕ)^4659*50000000000000000000^1024 ≤ 2321940186287819^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11159 100000 2321940186287819 50000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11159/100000 : ℝ)) (X := (2321940186287819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4659/1024 : ℝ) ≤ (20612307653201431/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4659 ≤ (20612307653201431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4659*100000000000000000000^1024 ≤ 20612307653201431^1024*25000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 20612307653201431 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (20612307653201431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002321940186287819/25000000000000000000 : ℝ) ≤ (10000204127976631/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (25002321940186287819/25000000000000000000 : ℝ)^1024 ≤ (10000204127976631/10000000000000000 : ℝ)^4659 := by
      have hnat : (25002321940186287819 : ℕ)^1024*10000000000000000^4659 ≤ 10000204127976631^4659*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002321940186287819 25000000000000000000 10000204127976631 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000204127976631/10000000000000000 : ℝ)) (X := (25002321940186287819/25000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025256188025777069/100000000000000000000 : ℝ) ≤ (10000555050199947/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (100025256188025777069/100000000000000000000 : ℝ)^1024 ≤ (10000555050199947/10000000000000000 : ℝ)^4659 := by
      have hnat : (100025256188025777069 : ℕ)^1024*10000000000000000^4659 ≤ 10000555050199947^4659*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025256188025777069 100000000000000000000 10000555050199947 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000555050199947/10000000000000000 : ℝ)) (X := (100025256188025777069/100000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020612307653201431/50000000000000000000 : ℝ) ≤ (10000905972423263/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50020612307653201431/50000000000000000000 : ℝ)^1024 ≤ (10000905972423263/10000000000000000 : ℝ)^4659 := by
      have hnat : (50020612307653201431 : ℕ)^1024*10000000000000000^4659 ≤ 10000905972423263^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020612307653201431 50000000000000000000 10000905972423263 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000905972423263/10000000000000000 : ℝ)) (X := (50020612307653201431/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2321940186287819/50000000000000000000 : ℝ) ≤ ((43243050971318962587/43250000000000000000 : ℝ)+2*(87730555829/108125000000000 : ℝ)*(11159/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (43243050971318962587/43250000000000000000 : ℝ)+2*(87730555829/108125000000000 : ℝ)*(11159/100000 : ℝ)=(10000204127976631/10000000000000000 : ℝ) by norm_num, show 1+2*(2321940186287819/50000000000000000000 : ℝ)=(25002321940186287819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20612307653201431/100000000000000000000 : ℝ)+(2321940186287819/50000000000000000000 : ℝ) ≤ ((43243050971318962587/43250000000000000000 : ℝ)+(87730555829/108125000000000 : ℝ)*((3871/25000 : ℝ)+(11159/100000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (43243050971318962587/43250000000000000000 : ℝ)+(87730555829/108125000000000 : ℝ)*((3871/25000 : ℝ)+(11159/100000 : ℝ))=(10000555050199947/10000000000000000 : ℝ) by norm_num, show 1+(20612307653201431/100000000000000000000 : ℝ)+(2321940186287819/50000000000000000000 : ℝ)=(100025256188025777069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20612307653201431/100000000000000000000 : ℝ) ≤ ((43243050971318962587/43250000000000000000 : ℝ)+2*(87730555829/108125000000000 : ℝ)*(3871/25000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (43243050971318962587/43250000000000000000 : ℝ)+2*(87730555829/108125000000000 : ℝ)*(3871/25000 : ℝ)=(10000905972423263/10000000000000000 : ℝ) by norm_num, show 1+2*(20612307653201431/100000000000000000000 : ℝ)=(50020612307653201431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43243050971318962587/43250000000000000000 : ℝ)*(X 1 0+X 2 0)+(87730555829/108125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43243050971318962587/43250000000000000000 : ℝ)) (alpha := (87730555829/108125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43243050971318962587/43250000000000000000 : ℝ)*(X 0 1+X 2 1)+(87730555829/108125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43243050971318962587/43250000000000000000 : ℝ)) (alpha := (87730555829/108125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43243050971318962587/43250000000000000000 : ℝ)*(X 0 2+X 1 2)+(87730555829/108125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43243050971318962587/43250000000000000000 : ℝ)) (alpha := (87730555829/108125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27646113/156250000 : ℝ)*X 0 0+(1084853583/2000000000 : ℝ)*X 0 1+(2610227401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334215399/625000000 : ℝ)*X 1 0+(-1873596573/10000000000 : ℝ)*X 1 1+(5220454911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069489279/2000000000 : ℝ)*X 2 0+(5220454891/10000000000 : ℝ)*X 2 1+(-234199573/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((423825153/1000000000 : ℝ)*X 0 0+(2000647031/5000000000 : ℝ)*X 0 1+(4486342213/10000000000 : ℝ)*X 0 2+(423825153/1000000000 : ℝ)*X 1 0+(2000647031/5000000000 : ℝ)*X 1 1+(4486342213/10000000000 : ℝ)*X 1 2+(423825153/1000000000 : ℝ)*X 2 0+(2000647031/5000000000 : ℝ)*X 2 1+(4486342213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1769377559/10000000000 : ℝ)*X 0 0+(1305379829/2500000000 : ℝ)*X 0 1+(5423195553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2119157241/5000000000 : ℝ)*X 0 0+(896761873/2000000000 : ℝ)*X 0 1+(2001922709/5000000000 : ℝ)*X 0 2+(2119157241/5000000000 : ℝ)*X 1 0+(896761873/2000000000 : ℝ)*X 1 1+(2001922709/5000000000 : ℝ)*X 1 2+(2119157241/5000000000 : ℝ)*X 2 0+(896761873/2000000000 : ℝ)*X 2 1+(2001922709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3260783275586161157302098489/1081250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242257967/50000000000000 : ℝ)*(base19) + (223651287/50000000000000 : ℝ)*(base23) + (65285833/100000000000000 : ℝ)*(upper3) + (25296769/100000000000000 : ℝ)*(upper4) + (22629173/100000000000000 : ℝ)*(upper5) + (1742033748963751/50000000000000 : ℝ)*(major0) + (1742033748963751/50000000000000 : ℝ)*(major1) + (1742033748963751/50000000000000 : ℝ)*(major2) + (4906467116020609/100000000000000 : ℝ)*(sp0) + (1226619367880817/25000000000000 : ℝ)*(sp1) + (1226619377184157/25000000000000 : ℝ)*(sp2) + (8246614537549/400000000000 : ℝ)*(sp3) + (10840018593/100000000000000 : ℝ)*(sp4) + (413112929/12500000000000 : ℝ)*(sp5) + (1030828469645341/50000000000000 : ℝ)*(f.failure) + (2453238978019601/50000000000000 : ℝ)*(f.sum) + (178817423139507/21625000000000000000000000000 : ℝ)*base65 + (6178047577067716163/2162500000000000000000000000000000 : ℝ)*base68 + (12133705360307283837/2162500000000000000000000000000000 : ℝ)*base69 + (27652308221569783837/2162500000000000000000000000000000 : ℝ)*base71 + (4483337926171/2703125000000000000000000000 : ℝ)*base74 + (8845653884355216163/2162500000000000000000000000000000 : ℝ)*base76 + (6103875539019783837/2162500000000000000000000000000000 : ℝ)*base77 + (7127069022619783837/2162500000000000000000000000000000 : ℝ)*base79 + (51353251468191/10812500000000000000000000000 : ℝ)*base81 + (23852679/2500000000000000000000 : ℝ)*base90 + (23852679/2500000000000000000000 : ℝ)*base92 + (23852679/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1582_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1582_box_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-31348969/200000000 : ℝ)*x 0 + (5395309473/10000000000 : ℝ)*x 1 + (674413643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31348969/200000000 : ℝ)^4661 ≤ (36337862669/390625000000 : ℝ)^3637 := by
    have hnat : (31348969 : ℕ)^4661*390625000000^3637 ≤ 36337862669^3637*200000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31348969 200000000 36337862669 390625000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395309473/10000000000 : ℝ)^4661 ≤ (5668594418359/12500000000000 : ℝ)^3637 := by
    have hnat : (5395309473 : ℕ)^4661*12500000000000^3637 ≤ 5668594418359^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395309473 10000000000 5668594418359 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674413643/1250000000 : ℝ)^4661 ≤ (22674375901489/50000000000000 : ℝ)^3637 := by
    have hnat : (674413643 : ℕ)^4661*50000000000000^3637 ≤ 22674375901489^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674413643 1250000000 22674375901489 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31348969/200000000 : ℝ), (5395309473/10000000000 : ℝ), (674413643/1250000000 : ℝ)] ![(36337862669/390625000000 : ℝ), (5668594418359/12500000000000 : ℝ), (22674375901489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31348969/200000000 : ℝ)|^4661 ≤ (36337862669/390625000000 : ℝ)^3637
        have hw : |(-31348969/200000000 : ℝ)|=(31348969/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395309473/10000000000 : ℝ)|^4661 ≤ (5668594418359/12500000000000 : ℝ)^3637
        have hw : |(5395309473/10000000000 : ℝ)|=(5395309473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674413643/1250000000 : ℝ)|^4661 ≤ (22674375901489/50000000000000 : ℝ)^3637
        have hw : |(674413643/1250000000 : ℝ)|=(674413643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271132107/10000000000 : ℝ)*x 0 + (-435032961/2500000000 : ℝ)*x 1 + (1348827353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271132107/10000000000 : ℝ)^4661 ≤ (22007755158179/50000000000000 : ℝ)^3637 := by
    have hnat : (5271132107 : ℕ)^4661*50000000000000^3637 ≤ 22007755158179^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271132107 10000000000 22007755158179 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435032961/2500000000 : ℝ)^4661 ≤ (10635734974469/100000000000000 : ℝ)^3637 := by
    have hnat : (435032961 : ℕ)^4661*100000000000000^3637 ≤ 10635734974469^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435032961 2500000000 10635734974469 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348827353/2500000000 : ℝ)^4661 ≤ (22674377344899/50000000000000 : ℝ)^3637 := by
    have hnat : (1348827353 : ℕ)^4661*50000000000000^3637 ≤ 22674377344899^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348827353 2500000000 22674377344899 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271132107/10000000000 : ℝ), (-435032961/2500000000 : ℝ), (1348827353/2500000000 : ℝ)] ![(22007755158179/50000000000000 : ℝ), (10635734974469/100000000000000 : ℝ), (22674377344899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271132107/10000000000 : ℝ)|^4661 ≤ (22007755158179/50000000000000 : ℝ)^3637
        have hw : |(5271132107/10000000000 : ℝ)|=(5271132107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435032961/2500000000 : ℝ)|^4661 ≤ (10635734974469/100000000000000 : ℝ)^3637
        have hw : |(-435032961/2500000000 : ℝ)|=(435032961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348827353/2500000000 : ℝ)|^4661 ≤ (22674377344899/50000000000000 : ℝ)^3637
        have hw : |(1348827353/2500000000 : ℝ)|=(1348827353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658891539/1250000000 : ℝ)*x 0 + (5395309347/10000000000 : ℝ)*x 1 + (-870065827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658891539/1250000000 : ℝ)^4661 ≤ (4401551251013/10000000000000 : ℝ)^3637 := by
    have hnat : (658891539 : ℕ)^4661*10000000000000^3637 ≤ 4401551251013^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658891539 1250000000 4401551251013 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395309347/10000000000 : ℝ)^4661 ≤ (11337188497409/25000000000000 : ℝ)^3637 := by
    have hnat : (5395309347 : ℕ)^4661*25000000000000^3637 ≤ 11337188497409^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395309347 10000000000 11337188497409 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870065827/5000000000 : ℝ)^4661 ≤ (10635733486223/100000000000000 : ℝ)^3637 := by
    have hnat : (870065827 : ℕ)^4661*100000000000000^3637 ≤ 10635733486223^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870065827 5000000000 10635733486223 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658891539/1250000000 : ℝ), (5395309347/10000000000 : ℝ), (-870065827/5000000000 : ℝ)] ![(4401551251013/10000000000000 : ℝ), (11337188497409/25000000000000 : ℝ), (10635733486223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658891539/1250000000 : ℝ)|^4661 ≤ (4401551251013/10000000000000 : ℝ)^3637
        have hw : |(658891539/1250000000 : ℝ)|=(658891539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395309347/10000000000 : ℝ)|^4661 ≤ (11337188497409/25000000000000 : ℝ)^3637
        have hw : |(5395309347/10000000000 : ℝ)|=(5395309347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-870065827/5000000000 : ℝ)|^4661 ≤ (10635733486223/100000000000000 : ℝ)^3637
        have hw : |(-870065827/5000000000 : ℝ)|=(870065827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4438504851/10000000000 : ℝ)*x 0 + (2072347009/5000000000 : ℝ)*x 1 + (4144694167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4438504851/10000000000 : ℝ)^4661 ≤ (35311481138577/100000000000000 : ℝ)^3637 := by
    have hnat : (4438504851 : ℕ)^4661*100000000000000^3637 ≤ 35311481138577^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438504851 10000000000 35311481138577 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072347009/5000000000 : ℝ)^4661 ≤ (32344258681/100000000000 : ℝ)^3637 := by
    have hnat : (2072347009 : ℕ)^4661*100000000000^3637 ≤ 32344258681^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072347009 5000000000 32344258681 100000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144694167/10000000000 : ℝ)^4661 ≤ (32344260171139/100000000000000 : ℝ)^3637 := by
    have hnat : (4144694167 : ℕ)^4661*100000000000000^3637 ≤ 32344260171139^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144694167 10000000000 32344260171139 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4438504851/10000000000 : ℝ), (2072347009/5000000000 : ℝ), (4144694167/10000000000 : ℝ)] ![(35311481138577/100000000000000 : ℝ), (32344258681/100000000000 : ℝ), (32344260171139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4438504851/10000000000 : ℝ)|^4661 ≤ (35311481138577/100000000000000 : ℝ)^3637
        have hw : |(4438504851/10000000000 : ℝ)|=(4438504851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072347009/5000000000 : ℝ)|^4661 ≤ (32344258681/100000000000 : ℝ)^3637
        have hw : |(2072347009/5000000000 : ℝ)|=(2072347009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144694167/10000000000 : ℝ)|^4661 ≤ (32344260171139/100000000000000 : ℝ)^3637
        have hw : |(4144694167/10000000000 : ℝ)|=(4144694167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976631853/10000000000 : ℝ)*x 0 + (1049049779/2000000000 : ℝ)*x 1 + (1049049847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976631853/10000000000 : ℝ)^4661 ≤ (6261280886577/50000000000000 : ℝ)^3637 := by
    have hnat : (1976631853 : ℕ)^4661*50000000000000^3637 ≤ 6261280886577^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976631853 10000000000 6261280886577 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049049779/2000000000 : ℝ)^4661 ≤ (43738717289997/100000000000000 : ℝ)^3637 := by
    have hnat : (1049049779 : ℕ)^4661*100000000000000^3637 ≤ 43738717289997^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049049779 2000000000 43738717289997 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049049847/2000000000 : ℝ)^4661 ≤ (4373872092341/10000000000000 : ℝ)^3637 := by
    have hnat : (1049049847 : ℕ)^4661*10000000000000^3637 ≤ 4373872092341^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049049847 2000000000 4373872092341 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976631853/10000000000 : ℝ), (1049049779/2000000000 : ℝ), (1049049847/2000000000 : ℝ)] ![(6261280886577/50000000000000 : ℝ), (43738717289997/100000000000000 : ℝ), (4373872092341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976631853/10000000000 : ℝ)|^4661 ≤ (6261280886577/50000000000000 : ℝ)^3637
        have hw : |(-1976631853/10000000000 : ℝ)|=(1976631853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049049779/2000000000 : ℝ)|^4661 ≤ (43738717289997/100000000000000 : ℝ)^3637
        have hw : |(1049049779/2000000000 : ℝ)|=(1049049779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049049847/2000000000 : ℝ)|^4661 ≤ (4373872092341/10000000000000 : ℝ)^3637
        have hw : |(1049049847/2000000000 : ℝ)|=(1049049847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335941201/625000000 : ℝ)*x 0 + (-901493063/5000000000 : ℝ)*x 1 + (2622624223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335941201/625000000 : ℝ)^4661 ≤ (22565370364167/50000000000000 : ℝ)^3637 := by
    have hnat : (335941201 : ℕ)^4661*50000000000000^3637 ≤ 22565370364167^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335941201 625000000 22565370364167 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901493063/5000000000 : ℝ)^4661 ≤ (5565273382627/50000000000000 : ℝ)^3637 := by
    have hnat : (901493063 : ℕ)^4661*50000000000000^3637 ≤ 5565273382627^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901493063 5000000000 5565273382627 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622624223/5000000000 : ℝ)^4661 ≤ (10934678122939/25000000000000 : ℝ)^3637 := by
    have hnat : (2622624223 : ℕ)^4661*25000000000000^3637 ≤ 10934678122939^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622624223 5000000000 10934678122939 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335941201/625000000 : ℝ), (-901493063/5000000000 : ℝ), (2622624223/5000000000 : ℝ)] ![(22565370364167/50000000000000 : ℝ), (5565273382627/50000000000000 : ℝ), (10934678122939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335941201/625000000 : ℝ)|^4661 ≤ (22565370364167/50000000000000 : ℝ)^3637
        have hw : |(335941201/625000000 : ℝ)|=(335941201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901493063/5000000000 : ℝ)|^4661 ≤ (5565273382627/50000000000000 : ℝ)^3637
        have hw : |(-901493063/5000000000 : ℝ)|=(901493063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622624223/5000000000 : ℝ)|^4661 ≤ (10934678122939/25000000000000 : ℝ)^3637
        have hw : |(2622624223/5000000000 : ℝ)|=(2622624223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375058621/10000000000 : ℝ)*x 0 + (5245248697/10000000000 : ℝ)*x 1 + (-1802986597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375058621/10000000000 : ℝ)^4661 ≤ (22565367162973/50000000000000 : ℝ)^3637 := by
    have hnat : (5375058621 : ℕ)^4661*50000000000000^3637 ≤ 22565367162973^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375058621 10000000000 22565367162973 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245248697/10000000000 : ℝ)^4661 ≤ (43738715174069/100000000000000 : ℝ)^3637 := by
    have hnat : (5245248697 : ℕ)^4661*100000000000000^3637 ≤ 43738715174069^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245248697 10000000000 43738715174069 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802986597/10000000000 : ℝ)^4661 ≤ (11130550491579/100000000000000 : ℝ)^3637 := by
    have hnat : (1802986597 : ℕ)^4661*100000000000000^3637 ≤ 11130550491579^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802986597 10000000000 11130550491579 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375058621/10000000000 : ℝ), (5245248697/10000000000 : ℝ), (-1802986597/10000000000 : ℝ)] ![(22565367162973/50000000000000 : ℝ), (43738715174069/100000000000000 : ℝ), (11130550491579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375058621/10000000000 : ℝ)|^4661 ≤ (22565367162973/50000000000000 : ℝ)^3637
        have hw : |(5375058621/10000000000 : ℝ)|=(5375058621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245248697/10000000000 : ℝ)|^4661 ≤ (43738715174069/100000000000000 : ℝ)^3637
        have hw : |(5245248697/10000000000 : ℝ)|=(5245248697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802986597/10000000000 : ℝ)|^4661 ≤ (11130550491579/100000000000000 : ℝ)^3637
        have hw : |(-1802986597/10000000000 : ℝ)|=(1802986597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (807050871/2000000000 : ℝ)*x 0 + (271637099/625000000 : ℝ)*x 1 + (434619277/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807050871/2000000000 : ℝ)^4661 ≤ (3906731792833/12500000000000 : ℝ)^3637 := by
    have hnat : (807050871 : ℕ)^4661*12500000000000^3637 ≤ 3906731792833^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807050871 2000000000 3906731792833 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271637099/625000000 : ℝ)^4661 ≤ (34373076949089/100000000000000 : ℝ)^3637 := by
    have hnat : (271637099 : ℕ)^4661*100000000000000^3637 ≤ 34373076949089^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271637099 625000000 34373076949089 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434619277/1000000000 : ℝ)^4661 ≤ (34373068698793/100000000000000 : ℝ)^3637 := by
    have hnat : (434619277 : ℕ)^4661*100000000000000^3637 ≤ 34373068698793^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434619277 1000000000 34373068698793 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(807050871/2000000000 : ℝ), (271637099/625000000 : ℝ), (434619277/1000000000 : ℝ)] ![(3906731792833/12500000000000 : ℝ), (34373076949089/100000000000000 : ℝ), (34373068698793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(807050871/2000000000 : ℝ)|^4661 ≤ (3906731792833/12500000000000 : ℝ)^3637
        have hw : |(807050871/2000000000 : ℝ)|=(807050871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271637099/625000000 : ℝ)|^4661 ≤ (34373076949089/100000000000000 : ℝ)^3637
        have hw : |(271637099/625000000 : ℝ)|=(271637099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(434619277/1000000000 : ℝ)|^4661 ≤ (34373068698793/100000000000000 : ℝ)^3637
        have hw : |(434619277/1000000000 : ℝ)|=(434619277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_8 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118115669/625000000 : ℝ)*x 0 + (5139403051/10000000000 : ℝ)*x 1 + (2707770113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118115669/625000000 : ℝ)^4661 ≤ (2364477180127/20000000000000 : ℝ)^3637 := by
    have hnat : (118115669 : ℕ)^4661*20000000000000^3637 ≤ 2364477180127^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118115669 625000000 2364477180127 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139403051/10000000000 : ℝ)^4661 ≤ (42610823928433/100000000000000 : ℝ)^3637 := by
    have hnat : (5139403051 : ℕ)^4661*100000000000000^3637 ≤ 42610823928433^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139403051 10000000000 42610823928433 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707770113/5000000000 : ℝ)^4661 ≤ (1822671606429/4000000000000 : ℝ)^3637 := by
    have hnat : (2707770113 : ℕ)^4661*4000000000000^3637 ≤ 1822671606429^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707770113 5000000000 1822671606429 4000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118115669/625000000 : ℝ), (5139403051/10000000000 : ℝ), (2707770113/5000000000 : ℝ)] ![(2364477180127/20000000000000 : ℝ), (42610823928433/100000000000000 : ℝ), (1822671606429/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118115669/625000000 : ℝ)|^4661 ≤ (2364477180127/20000000000000 : ℝ)^3637
        have hw : |(-118115669/625000000 : ℝ)|=(118115669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139403051/10000000000 : ℝ)|^4661 ≤ (42610823928433/100000000000000 : ℝ)^3637
        have hw : |(5139403051/10000000000 : ℝ)|=(5139403051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707770113/5000000000 : ℝ)|^4661 ≤ (1822671606429/4000000000000 : ℝ)^3637
        have hw : |(2707770113/5000000000 : ℝ)|=(2707770113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_9 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52571181/100000000 : ℝ)*x 0 + (-865714401/5000000000 : ℝ)*x 1 + (2707770049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52571181/100000000 : ℝ)^4661 ≤ (21932799003377/50000000000000 : ℝ)^3637 := by
    have hnat : (52571181 : ℕ)^4661*50000000000000^3637 ≤ 21932799003377^3637*100000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52571181 100000000 21932799003377 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865714401/5000000000 : ℝ)^4661 ≤ (264190329871/2500000000000 : ℝ)^3637 := by
    have hnat : (865714401 : ℕ)^4661*2500000000000^3637 ≤ 264190329871^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865714401 5000000000 264190329871 2500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707770049/5000000000 : ℝ)^4661 ≤ (11391697195123/25000000000000 : ℝ)^3637 := by
    have hnat : (2707770049 : ℕ)^4661*25000000000000^3637 ≤ 11391697195123^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707770049 5000000000 11391697195123 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52571181/100000000 : ℝ), (-865714401/5000000000 : ℝ), (2707770049/5000000000 : ℝ)] ![(21932799003377/50000000000000 : ℝ), (264190329871/2500000000000 : ℝ), (11391697195123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52571181/100000000 : ℝ)|^4661 ≤ (21932799003377/50000000000000 : ℝ)^3637
        have hw : |(52571181/100000000 : ℝ)|=(52571181/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-865714401/5000000000 : ℝ)|^4661 ≤ (264190329871/2500000000000 : ℝ)^3637
        have hw : |(-865714401/5000000000 : ℝ)|=(865714401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707770049/5000000000 : ℝ)|^4661 ≤ (11391697195123/25000000000000 : ℝ)^3637
        have hw : |(2707770049/5000000000 : ℝ)|=(2707770049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_10 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257118183/10000000000 : ℝ)*x 0 + (5415540257/10000000000 : ℝ)*x 1 + (-173142847/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257118183/10000000000 : ℝ)^4661 ≤ (43865598894299/100000000000000 : ℝ)^3637 := by
    have hnat : (5257118183 : ℕ)^4661*100000000000000^3637 ≤ 43865598894299^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257118183 10000000000 43865598894299 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415540257/10000000000 : ℝ)^4661 ≤ (9113358099/20000000000 : ℝ)^3637 := by
    have hnat : (5415540257 : ℕ)^4661*20000000000^3637 ≤ 9113358099^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415540257 10000000000 9113358099 20000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173142847/1000000000 : ℝ)^4661 ≤ (2113522119599/20000000000000 : ℝ)^3637 := by
    have hnat : (173142847 : ℕ)^4661*20000000000000^3637 ≤ 2113522119599^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173142847 1000000000 2113522119599 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257118183/10000000000 : ℝ), (5415540257/10000000000 : ℝ), (-173142847/1000000000 : ℝ)] ![(43865598894299/100000000000000 : ℝ), (9113358099/20000000000 : ℝ), (2113522119599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257118183/10000000000 : ℝ)|^4661 ≤ (43865598894299/100000000000000 : ℝ)^3637
        have hw : |(5257118183/10000000000 : ℝ)|=(5257118183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415540257/10000000000 : ℝ)|^4661 ≤ (9113358099/20000000000 : ℝ)^3637
        have hw : |(5415540257/10000000000 : ℝ)|=(5415540257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173142847/1000000000 : ℝ)|^4661 ≤ (2113522119599/20000000000000 : ℝ)^3637
        have hw : |(-173142847/1000000000 : ℝ)|=(173142847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_11 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4491726733/10000000000 : ℝ)*x 0 + (4117494207/10000000000 : ℝ)*x 1 + (823498839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491726733/10000000000 : ℝ)^4661 ≤ (35855026330429/100000000000000 : ℝ)^3637 := by
    have hnat : (4491726733 : ℕ)^4661*100000000000000^3637 ≤ 35855026330429^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491726733 10000000000 35855026330429 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117494207/10000000000 : ℝ)^4661 ≤ (16036243445269/50000000000000 : ℝ)^3637 := by
    have hnat : (4117494207 : ℕ)^4661*50000000000000^3637 ≤ 16036243445269^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117494207 10000000000 16036243445269 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823498839/2000000000 : ℝ)^4661 ≤ (32072486770749/100000000000000 : ℝ)^3637 := by
    have hnat : (823498839 : ℕ)^4661*100000000000000^3637 ≤ 32072486770749^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823498839 2000000000 32072486770749 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491726733/10000000000 : ℝ), (4117494207/10000000000 : ℝ), (823498839/2000000000 : ℝ)] ![(35855026330429/100000000000000 : ℝ), (16036243445269/50000000000000 : ℝ), (32072486770749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491726733/10000000000 : ℝ)|^4661 ≤ (35855026330429/100000000000000 : ℝ)^3637
        have hw : |(4491726733/10000000000 : ℝ)|=(4491726733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4117494207/10000000000 : ℝ)|^4661 ≤ (16036243445269/50000000000000 : ℝ)^3637
        have hw : |(4117494207/10000000000 : ℝ)|=(4117494207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823498839/2000000000 : ℝ)|^4661 ≤ (32072486770749/100000000000000 : ℝ)^3637
        have hw : |(823498839/2000000000 : ℝ)|=(823498839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_12 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413459451/2500000000 : ℝ)*x 0 + (1099592609/2000000000 : ℝ)*x 1 + (5230199867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413459451/2500000000 : ℝ)^4661 ≤ (9964580631617/100000000000000 : ℝ)^3637 := by
    have hnat : (413459451 : ℕ)^4661*100000000000000^3637 ≤ 9964580631617^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413459451 2500000000 9964580631617 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099592609/2000000000 : ℝ)^4661 ≤ (46457458592053/100000000000000 : ℝ)^3637 := by
    have hnat : (1099592609 : ℕ)^4661*100000000000000^3637 ≤ 46457458592053^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099592609 2000000000 46457458592053 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230199867/10000000000 : ℝ)^4661 ≤ (43577960758247/100000000000000 : ℝ)^3637 := by
    have hnat : (5230199867 : ℕ)^4661*100000000000000^3637 ≤ 43577960758247^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230199867 10000000000 43577960758247 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413459451/2500000000 : ℝ), (1099592609/2000000000 : ℝ), (5230199867/10000000000 : ℝ)] ![(9964580631617/100000000000000 : ℝ), (46457458592053/100000000000000 : ℝ), (43577960758247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413459451/2500000000 : ℝ)|^4661 ≤ (9964580631617/100000000000000 : ℝ)^3637
        have hw : |(-413459451/2500000000 : ℝ)|=(413459451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099592609/2000000000 : ℝ)|^4661 ≤ (46457458592053/100000000000000 : ℝ)^3637
        have hw : |(1099592609/2000000000 : ℝ)|=(1099592609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230199867/10000000000 : ℝ)|^4661 ≤ (43577960758247/100000000000000 : ℝ)^3637
        have hw : |(5230199867/10000000000 : ℝ)|=(5230199867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_13 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134637071/250000000 : ℝ)*x 0 + (-22614011/125000000 : ℝ)*x 1 + (2615099989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134637071/250000000 : ℝ)^4661 ≤ (11310733204591/25000000000000 : ℝ)^3637 := by
    have hnat : (134637071 : ℕ)^4661*25000000000000^3637 ≤ 11310733204591^3637*250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134637071 250000000 11310733204591 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22614011/125000000 : ℝ)^4661 ≤ (1117910522183/10000000000000 : ℝ)^3637 := by
    have hnat : (22614011 : ℕ)^4661*10000000000000^3637 ≤ 1117910522183^3637*125000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22614011 125000000 1117910522183 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615099989/5000000000 : ℝ)^4661 ≤ (4357796194349/10000000000000 : ℝ)^3637 := by
    have hnat : (2615099989 : ℕ)^4661*10000000000000^3637 ≤ 4357796194349^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615099989 5000000000 4357796194349 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134637071/250000000 : ℝ), (-22614011/125000000 : ℝ), (2615099989/5000000000 : ℝ)] ![(11310733204591/25000000000000 : ℝ), (1117910522183/10000000000000 : ℝ), (4357796194349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134637071/250000000 : ℝ)|^4661 ≤ (11310733204591/25000000000000 : ℝ)^3637
        have hw : |(134637071/250000000 : ℝ)|=(134637071/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22614011/125000000 : ℝ)|^4661 ≤ (1117910522183/10000000000000 : ℝ)^3637
        have hw : |(-22614011/125000000 : ℝ)|=(22614011/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615099989/5000000000 : ℝ)|^4661 ≤ (4357796194349/10000000000000 : ℝ)^3637
        have hw : |(2615099989/5000000000 : ℝ)|=(2615099989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_14 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385482917/10000000000 : ℝ)*x 0 + (1307549947/2500000000 : ℝ)*x 1 + (-1809121031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385482917/10000000000 : ℝ)^4661 ≤ (45242933647361/100000000000000 : ℝ)^3637 := by
    have hnat : (5385482917 : ℕ)^4661*100000000000000^3637 ≤ 45242933647361^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385482917 10000000000 45242933647361 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307549947/2500000000 : ℝ)^4661 ≤ (8715591982939/20000000000000 : ℝ)^3637 := by
    have hnat : (1307549947 : ℕ)^4661*20000000000000^3637 ≤ 8715591982939^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307549947 2500000000 8715591982939 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1809121031/10000000000 : ℝ)^4661 ≤ (11179106417613/100000000000000 : ℝ)^3637 := by
    have hnat : (1809121031 : ℕ)^4661*100000000000000^3637 ≤ 11179106417613^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809121031 10000000000 11179106417613 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385482917/10000000000 : ℝ), (1307549947/2500000000 : ℝ), (-1809121031/10000000000 : ℝ)] ![(45242933647361/100000000000000 : ℝ), (8715591982939/20000000000000 : ℝ), (11179106417613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385482917/10000000000 : ℝ)|^4661 ≤ (45242933647361/100000000000000 : ℝ)^3637
        have hw : |(5385482917/10000000000 : ℝ)|=(5385482917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307549947/2500000000 : ℝ)|^4661 ≤ (8715591982939/20000000000000 : ℝ)^3637
        have hw : |(1307549947/2500000000 : ℝ)|=(1307549947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1809121031/10000000000 : ℝ)|^4661 ≤ (11179106417613/100000000000000 : ℝ)^3637
        have hw : |(-1809121031/10000000000 : ℝ)|=(1809121031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_box_15 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (249621839/625000000 : ℝ)*x 0 + (4366376133/10000000000 : ℝ)*x 1 + (2183188027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249621839/625000000 : ℝ)^4661 ≤ (6168891862139/20000000000000 : ℝ)^3637 := by
    have hnat : (249621839 : ℕ)^4661*20000000000000^3637 ≤ 6168891862139^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249621839 625000000 6168891862139 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4366376133/10000000000 : ℝ)^4661 ≤ (34577770736579/100000000000000 : ℝ)^3637 := by
    have hnat : (4366376133 : ℕ)^4661*100000000000000^3637 ≤ 34577770736579^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366376133 10000000000 34577770736579 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183188027/5000000000 : ℝ)^4661 ≤ (3457776993483/10000000000000 : ℝ)^3637 := by
    have hnat : (2183188027 : ℕ)^4661*10000000000000^3637 ≤ 3457776993483^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183188027 5000000000 3457776993483 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249621839/625000000 : ℝ), (4366376133/10000000000 : ℝ), (2183188027/5000000000 : ℝ)] ![(6168891862139/20000000000000 : ℝ), (34577770736579/100000000000000 : ℝ), (3457776993483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249621839/625000000 : ℝ)|^4661 ≤ (6168891862139/20000000000000 : ℝ)^3637
        have hw : |(249621839/625000000 : ℝ)|=(249621839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4366376133/10000000000 : ℝ)|^4661 ≤ (34577770736579/100000000000000 : ℝ)^3637
        have hw : |(4366376133/10000000000 : ℝ)|=(4366376133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2183188027/5000000000 : ℝ)|^4661 ≤ (3457776993483/10000000000000 : ℝ)^3637
        have hw : |(2183188027/5000000000 : ℝ)|=(2183188027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(1277/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(737/1250 : ℝ) ∧ (81039/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2161/2500 : ℝ) := by
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
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (4659/1024 : ℝ) ≤ (232288705023579/5000000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^4659 ≤ (232288705023579/5000000000000000000 : ℝ)^1024 := by
      have hnat : (279 : ℕ)^4659*5000000000000000000^1024 ≤ 232288705023579^1024*2500^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 232288705023579 5000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (232288705023579/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4659/1024 : ℝ) ≤ (20612307653201431/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4659 ≤ (20612307653201431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4659*100000000000000000000^1024 ≤ 20612307653201431^1024*25000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 20612307653201431 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (20612307653201431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500232288705023579/2500000000000000000 : ℝ) ≤ (5000102105607479/5000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (2500232288705023579/2500000000000000000 : ℝ)^1024 ≤ (5000102105607479/5000000000000000 : ℝ)^4659 := by
      have hnat : (2500232288705023579 : ℕ)^1024*5000000000000000^4659 ≤ 5000102105607479^4659*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500232288705023579 2500000000000000000 5000102105607479 5000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000102105607479/5000000000000000 : ℝ)) (X := (2500232288705023579/2500000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025258081753673011/100000000000000000000 : ℝ) ≤ (10000555091813927/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (100025258081753673011/100000000000000000000 : ℝ)^1024 ≤ (10000555091813927/10000000000000000 : ℝ)^4659 := by
      have hnat : (100025258081753673011 : ℕ)^1024*10000000000000000^4659 ≤ 10000555091813927^4659*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025258081753673011 100000000000000000000 10000555091813927 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000555091813927/10000000000000000 : ℝ)) (X := (100025258081753673011/100000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020612307653201431/50000000000000000000 : ℝ) ≤ (312528311637903/312500000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50020612307653201431/50000000000000000000 : ℝ)^1024 ≤ (312528311637903/312500000000000 : ℝ)^4659 := by
      have hnat : (50020612307653201431 : ℕ)^1024*312500000000000^4659 ≤ 312528311637903^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020612307653201431 50000000000000000000 312528311637903 312500000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312528311637903/312500000000000 : ℝ)) (X := (50020612307653201431/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(232288705023579/5000000000000000000 : ℝ) ≤ ((5404131419290561289/5405000000000000000 : ℝ)+2*(350880598969/432400000000000 : ℝ)*(279/2500 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (5404131419290561289/5405000000000000000 : ℝ)+2*(350880598969/432400000000000 : ℝ)*(279/2500 : ℝ)=(5000102105607479/5000000000000000 : ℝ) by norm_num, show 1+2*(232288705023579/5000000000000000000 : ℝ)=(2500232288705023579/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20612307653201431/100000000000000000000 : ℝ)+(232288705023579/5000000000000000000 : ℝ) ≤ ((5404131419290561289/5405000000000000000 : ℝ)+(350880598969/432400000000000 : ℝ)*((3871/25000 : ℝ)+(279/2500 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (5404131419290561289/5405000000000000000 : ℝ)+(350880598969/432400000000000 : ℝ)*((3871/25000 : ℝ)+(279/2500 : ℝ))=(10000555091813927/10000000000000000 : ℝ) by norm_num, show 1+(20612307653201431/100000000000000000000 : ℝ)+(232288705023579/5000000000000000000 : ℝ)=(100025258081753673011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20612307653201431/100000000000000000000 : ℝ) ≤ ((5404131419290561289/5405000000000000000 : ℝ)+2*(350880598969/432400000000000 : ℝ)*(3871/25000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (5404131419290561289/5405000000000000000 : ℝ)+2*(350880598969/432400000000000 : ℝ)*(3871/25000 : ℝ)=(312528311637903/312500000000000 : ℝ) by norm_num, show 1+2*(20612307653201431/100000000000000000000 : ℝ)=(50020612307653201431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5404131419290561289/5405000000000000000 : ℝ)*(X 1 0+X 2 0)+(350880598969/432400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5404131419290561289/5405000000000000000 : ℝ)) (alpha := (350880598969/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5404131419290561289/5405000000000000000 : ℝ)*(X 0 1+X 2 1)+(350880598969/432400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5404131419290561289/5405000000000000000 : ℝ)) (alpha := (350880598969/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5404131419290561289/5405000000000000000 : ℝ)*(X 0 2+X 1 2)+(350880598969/432400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (5404131419290561289/5405000000000000000 : ℝ)) (alpha := (350880598969/432400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-31348969/200000000 : ℝ)*X 0 0+(5395309473/10000000000 : ℝ)*X 0 1+(674413643/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271132107/10000000000 : ℝ)*X 1 0+(-435032961/2500000000 : ℝ)*X 1 1+(1348827353/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((658891539/1250000000 : ℝ)*X 2 0+(5395309347/10000000000 : ℝ)*X 2 1+(-870065827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4438504851/10000000000 : ℝ)*X 0 0+(2072347009/5000000000 : ℝ)*X 0 1+(4144694167/10000000000 : ℝ)*X 0 2+(4438504851/10000000000 : ℝ)*X 1 0+(2072347009/5000000000 : ℝ)*X 1 1+(4144694167/10000000000 : ℝ)*X 1 2+(4438504851/10000000000 : ℝ)*X 2 0+(2072347009/5000000000 : ℝ)*X 2 1+(4144694167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1976631853/10000000000 : ℝ)*X 0 0+(1049049779/2000000000 : ℝ)*X 0 1+(1049049847/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335941201/625000000 : ℝ)*X 1 0+(-901493063/5000000000 : ℝ)*X 1 1+(2622624223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375058621/10000000000 : ℝ)*X 2 0+(5245248697/10000000000 : ℝ)*X 2 1+(-1802986597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((807050871/2000000000 : ℝ)*X 0 0+(271637099/625000000 : ℝ)*X 0 1+(434619277/1000000000 : ℝ)*X 0 2+(807050871/2000000000 : ℝ)*X 1 0+(271637099/625000000 : ℝ)*X 1 1+(434619277/1000000000 : ℝ)*X 1 2+(807050871/2000000000 : ℝ)*X 2 0+(271637099/625000000 : ℝ)*X 2 1+(434619277/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-118115669/625000000 : ℝ)*X 0 0+(5139403051/10000000000 : ℝ)*X 0 1+(2707770113/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((52571181/100000000 : ℝ)*X 1 0+(-865714401/5000000000 : ℝ)*X 1 1+(2707770049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257118183/10000000000 : ℝ)*X 2 0+(5415540257/10000000000 : ℝ)*X 2 1+(-173142847/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4491726733/10000000000 : ℝ)*X 0 0+(4117494207/10000000000 : ℝ)*X 0 1+(823498839/2000000000 : ℝ)*X 0 2+(4491726733/10000000000 : ℝ)*X 1 0+(4117494207/10000000000 : ℝ)*X 1 1+(823498839/2000000000 : ℝ)*X 1 2+(4491726733/10000000000 : ℝ)*X 2 0+(4117494207/10000000000 : ℝ)*X 2 1+(823498839/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-413459451/2500000000 : ℝ)*X 0 0+(1099592609/2000000000 : ℝ)*X 0 1+(5230199867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134637071/250000000 : ℝ)*X 1 0+(-22614011/125000000 : ℝ)*X 1 1+(2615099989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5385482917/10000000000 : ℝ)*X 2 0+(1307549947/2500000000 : ℝ)*X 2 1+(-1809121031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((249621839/625000000 : ℝ)*X 0 0+(4366376133/10000000000 : ℝ)*X 0 1+(2183188027/5000000000 : ℝ)*X 0 2+(249621839/625000000 : ℝ)*X 1 0+(4366376133/10000000000 : ℝ)*X 1 1+(2183188027/5000000000 : ℝ)*X 1 2+(249621839/625000000 : ℝ)*X 2 0+(4366376133/10000000000 : ℝ)*X 2 1+(2183188027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1277/2000 : ℝ) ≤ (-3751057753750147721179843718553/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128833147/50000000000000 : ℝ)*(upper1) + (20282819/20000000000000 : ℝ)*(upper2) + (158273853/100000000000000 : ℝ)*(lower4) + (5788459/20000000000000 : ℝ)*(upper5) + (1162458729441319/50000000000000 : ℝ)*(major0) + (1162458729441319/50000000000000 : ℝ)*(major1) + (1162458729441319/50000000000000 : ℝ)*(major2) + (155852531/100000000000000 : ℝ)*(sp1) + (784605307/12500000000000 : ℝ)*(sp2) + (441549283/25000000000000 : ℝ)*(sp3) + (1647687151193571/50000000000000 : ℝ)*(sp4) + (329537414653461/10000000000000 : ℝ)*(sp5) + (1647684012772343/50000000000000 : ℝ)*(sp6) + (137574144636539/10000000000000 : ℝ)*(sp7) + (687871606281261/50000000000000 : ℝ)*(f.failure) + (1647687151193571/50000000000000 : ℝ)*(f.sum) + (2904935967337/470000000000000000000000000 : ℝ)*base65 + (2755348644495117/11750000000000000000000000000000 : ℝ)*base67 + (76761860160495117/11750000000000000000000000000000 : ℝ)*base69 + (190030172331745117/11750000000000000000000000000000 : ℝ)*base71 + (2955338676983/470000000000000000000000000 : ℝ)*base74 + (176323117981995117/11750000000000000000000000000000 : ℝ)*base75 + (74817924344995117/11750000000000000000000000000000 : ℝ)*base77 + (37743296807495117/11750000000000000000000000000000 : ℝ)*base79 + (121945213997/470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14879159/2500000000000000000000 : ℝ)*base90 + (14879159/2500000000000000000000 : ℝ)*base92 + (14879159/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (737/1250 : ℝ) ≤ (79672841738099682918179643034641/135125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250173/2500000000000 : ℝ)*(upper0) + (1458697/2500000000000 : ℝ)*(lower1) + (96935277/100000000000000 : ℝ)*(upper4) + (1202988540357123/50000000000000 : ℝ)*(major0) + (1202988540357123/50000000000000 : ℝ)*(major1) + (1202988540357123/50000000000000 : ℝ)*(major2) + (3368586951188103/100000000000000 : ℝ)*(sp0) + (67371782459267/2000000000000 : ℝ)*(sp1) + (421073305045119/12500000000000 : ℝ)*(sp2) + (22245441207133/1562500000000 : ℝ)*(sp3) + (1617022957/100000000000000 : ℝ)*(sp5) + (1074906339/25000000000000 : ℝ)*(sp6) + (1075832141/100000000000000 : ℝ)*(sp7) + (757759641/20000000000000 : ℝ)*(sp8) + (1423709313088653/100000000000000 : ℝ)*(f.failure) + (842147684996577/25000000000000 : ℝ)*(f.sum) + (49403429087617/10810000000000000000000000000 : ℝ)*base65 + (2753273029856950953/270250000000000000000000000000000 : ℝ)*base68 + (1334444991022450953/270250000000000000000000000000000 : ℝ)*base70 + (577284674444299047/270250000000000000000000000000000 : ℝ)*base71 + (35942920601993/10810000000000000000000000000 : ℝ)*base74 + (1005447197437450953/270250000000000000000000000000000 : ℝ)*base76 + (1907008702550200953/270250000000000000000000000000000 : ℝ)*base78 + (1731402404527549047/270250000000000000000000000000000 : ℝ)*base79 + (44030328660353/10810000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (46125993/5000000000000000000000 : ℝ)*base89 + (46125993/5000000000000000000000 : ℝ)*base91 + (46125993/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81039/100000 : ℝ) ≤ (109507340767892001165301361202879/135125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102753983/100000000000000 : ℝ)*(lower3) + (86965867/100000000000000 : ℝ)*(upper4) + (19704817/100000000000000 : ℝ)*(lower5) + (1295358611838521/50000000000000 : ℝ)*(major0) + (1295358611838521/50000000000000 : ℝ)*(major1) + (1295358611838521/50000000000000 : ℝ)*(major2) + (201051313/20000000000000 : ℝ)*(sp0) + (7220947679/25000000000000 : ℝ)*(sp1) + (69491344041/100000000000000 : ℝ)*(sp2) + (27810004237/100000000000000 : ℝ)*(sp3) + (3621392433759287/100000000000000 : ℝ)*(sp8) + (226335284701571/6250000000000 : ℝ)*(sp9) + (905330986917953/25000000000000 : ℝ)*(sp10) + (1532999361573483/100000000000000 : ℝ)*(sp11) + (1533027171577721/100000000000000 : ℝ)*(f.failure) + (905348359753963/25000000000000 : ℝ)*(f.sum) + (64370402738169/10810000000000000000000000000 : ℝ)*base65 + (2996857016019976069/270250000000000000000000000000000 : ℝ)*base67 + (1092747441165726069/270250000000000000000000000000000 : ℝ)*base69 + (2584573666887726069/270250000000000000000000000000000 : ℝ)*base71 + (24666057079339/10810000000000000000000000000 : ℝ)*base73 + (1812041301431226069/270250000000000000000000000000000 : ℝ)*base75 + (1182292311823726069/270250000000000000000000000000000 : ℝ)*base77 + (1277293552682726069/270250000000000000000000000000000 : ℝ)*base79 + (8472510183749/10810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15816101/5000000000000000000000 : ℝ)*base89 + (15816101/5000000000000000000000 : ℝ)*base91 + (15816101/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-2161/2500 : ℝ) ≤ (-58399098426474042998625268581243/67562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7627/100000000000 : ℝ)*(lower0) + (3884671/12500000000000 : ℝ)*(upper3) + (11103573/50000000000000 : ℝ)*(lower4) + (1315748169438921/50000000000000 : ℝ)*(major0) + (1315748169438921/50000000000000 : ℝ)*(major1) + (1315748169438921/50000000000000 : ℝ)*(major2) + (2096598399/100000000000000 : ℝ)*(sp4) + (2444478241/5000000000000 : ℝ)*(sp6) + (8552163049/100000000000000 : ℝ)*(sp7) + (19482989/5000000000000 : ℝ)*(sp8) + (186732241476379/5000000000000 : ℝ)*(sp12) + (1867323657892879/50000000000000 : ℝ)*(sp13) + (1867299213110469/50000000000000 : ℝ)*(sp14) + (194643649078247/12500000000000 : ℝ)*(sp15) + (62286309791561/4000000000000 : ℝ)*(f.failure) + (1867323657892879/50000000000000 : ℝ)*(f.sum) + (121208895572529/10810000000000000000000000000 : ℝ)*base65 + (2372370199084108331/270250000000000000000000000000000 : ℝ)*base68 + (889604098666608331/270250000000000000000000000000000 : ℝ)*base70 + (886071472433391669/270250000000000000000000000000000 : ℝ)*base71 + (3662707311409/10810000000000000000000000000 : ℝ)*base73 + (1552850680901358331/270250000000000000000000000000000 : ℝ)*base76 + (1362580581148108331/270250000000000000000000000000000 : ℝ)*base78 + (1054904610738858331/270250000000000000000000000000000 : ℝ)*base80 + (43495520361489/10810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1465141/200000000000000000000 : ℝ)*base89 + (1465141/200000000000000000000 : ℝ)*base91 + (1465141/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1582_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1277/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(737/1250 : ℝ) else (81039/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2161/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1582_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1582_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1277/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(737/1250 : ℝ) else (81039/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2161/2500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1582_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1582_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1277/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(737/1250 : ℝ) else (81039/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2161/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
