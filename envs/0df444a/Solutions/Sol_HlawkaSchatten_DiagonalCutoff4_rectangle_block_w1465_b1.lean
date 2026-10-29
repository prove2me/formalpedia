-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:44.789594+00:00
-- url     : https://prove2.me/submissions/0da9eb0c-0e9b-40de-822a-06196764e8b3

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
theorem support_rectangle_w1465_s3_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938885159/10000000000 : ℝ)*x 0 + (680624341/1250000000 : ℝ)*x 1 + (2604940377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938885159/10000000000 : ℝ)^4427 ≤ (5917505965811/50000000000000 : ℝ)^3403 := by
    have hnat : (1938885159 : ℕ)^4427*50000000000000^3403 ≤ 5917505965811^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938885159 10000000000 5917505965811 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680624341/1250000000 : ℝ)^4427 ≤ (9069559668093/20000000000000 : ℝ)^3403 := by
    have hnat : (680624341 : ℕ)^4427*20000000000000^3403 ≤ 9069559668093^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680624341 1250000000 9069559668093 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2604940377/5000000000 : ℝ)^4427 ≤ (5352148714479/12500000000000 : ℝ)^3403 := by
    have hnat : (2604940377 : ℕ)^4427*12500000000000^3403 ≤ 5352148714479^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604940377 5000000000 5352148714479 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938885159/10000000000 : ℝ), (680624341/1250000000 : ℝ), (2604940377/5000000000 : ℝ)] ![(5917505965811/50000000000000 : ℝ), (9069559668093/20000000000000 : ℝ), (5352148714479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938885159/10000000000 : ℝ)|^4427 ≤ (5917505965811/50000000000000 : ℝ)^3403
        have hw : |(-1938885159/10000000000 : ℝ)|=(1938885159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680624341/1250000000 : ℝ)|^4427 ≤ (9069559668093/20000000000000 : ℝ)^3403
        have hw : |(680624341/1250000000 : ℝ)|=(680624341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2604940377/5000000000 : ℝ)|^4427 ≤ (5352148714479/12500000000000 : ℝ)^3403
        have hw : |(2604940377/5000000000 : ℝ)|=(2604940377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355510719/10000000000 : ℝ)*x 0 + (-2059560843/10000000000 : ℝ)*x 1 + (5209880227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355510719/10000000000 : ℝ)^4427 ≤ (44380696019549/100000000000000 : ℝ)^3403 := by
    have hnat : (5355510719 : ℕ)^4427*100000000000000^3403 ≤ 44380696019549^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355510719 10000000000 44380696019549 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059560843/10000000000 : ℝ)^4427 ≤ (3200529970313/25000000000000 : ℝ)^3403 := by
    have hnat : (2059560843 : ℕ)^4427*25000000000000^3403 ≤ 3200529970313^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059560843 10000000000 3200529970313 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5209880227/10000000000 : ℝ)^4427 ≤ (42817184081421/100000000000000 : ℝ)^3403 := by
    have hnat : (5209880227 : ℕ)^4427*100000000000000^3403 ≤ 42817184081421^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209880227 10000000000 42817184081421 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355510719/10000000000 : ℝ), (-2059560843/10000000000 : ℝ), (5209880227/10000000000 : ℝ)] ![(44380696019549/100000000000000 : ℝ), (3200529970313/25000000000000 : ℝ), (42817184081421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355510719/10000000000 : ℝ)|^4427 ≤ (44380696019549/100000000000000 : ℝ)^3403
        have hw : |(5355510719/10000000000 : ℝ)|=(5355510719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059560843/10000000000 : ℝ)|^4427 ≤ (3200529970313/25000000000000 : ℝ)^3403
        have hw : |(-2059560843/10000000000 : ℝ)|=(2059560843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5209880227/10000000000 : ℝ)|^4427 ≤ (42817184081421/100000000000000 : ℝ)^3403
        have hw : |(5209880227/10000000000 : ℝ)|=(5209880227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071102273/2000000000 : ℝ)*x 0 + (5209879601/10000000000 : ℝ)*x 1 + (-2059560811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071102273/2000000000 : ℝ)^4427 ≤ (22190351491891/50000000000000 : ℝ)^3403 := by
    have hnat : (1071102273 : ℕ)^4427*50000000000000^3403 ≤ 22190351491891^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071102273 2000000000 22190351491891 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5209879601/10000000000 : ℝ)^4427 ≤ (42817177388553/100000000000000 : ℝ)^3403 := by
    have hnat : (5209879601 : ℕ)^4427*100000000000000^3403 ≤ 42817177388553^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209879601 10000000000 42817177388553 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059560811/10000000000 : ℝ)^4427 ≤ (1600264952811/12500000000000 : ℝ)^3403 := by
    have hnat : (2059560811 : ℕ)^4427*12500000000000^3403 ≤ 1600264952811^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059560811 10000000000 1600264952811 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071102273/2000000000 : ℝ), (5209879601/10000000000 : ℝ), (-2059560811/10000000000 : ℝ)] ![(22190351491891/50000000000000 : ℝ), (42817177388553/100000000000000 : ℝ), (1600264952811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071102273/2000000000 : ℝ)|^4427 ≤ (22190351491891/50000000000000 : ℝ)^3403
        have hw : |(1071102273/2000000000 : ℝ)|=(1071102273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5209879601/10000000000 : ℝ)|^4427 ≤ (42817177388553/100000000000000 : ℝ)^3403
        have hw : |(5209879601/10000000000 : ℝ)|=(5209879601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059560811/10000000000 : ℝ)|^4427 ≤ (1600264952811/12500000000000 : ℝ)^3403
        have hw : |(-2059560811/10000000000 : ℝ)|=(2059560811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145817769/5000000000 : ℝ)*x 0 + (4040706089/10000000000 : ℝ)*x 1 + (4556239077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145817769/5000000000 : ℝ)^4427 ≤ (33271701920937/100000000000000 : ℝ)^3403 := by
    have hnat : (2145817769 : ℕ)^4427*100000000000000^3403 ≤ 33271701920937^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145817769 5000000000 33271701920937 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4040706089/10000000000 : ℝ)^4427 ≤ (3076351377839/10000000000000 : ℝ)^3403 := by
    have hnat : (4040706089 : ℕ)^4427*10000000000000^3403 ≤ 3076351377839^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040706089 10000000000 3076351377839 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556239077/10000000000 : ℝ)^4427 ≤ (17982392140339/50000000000000 : ℝ)^3403 := by
    have hnat : (4556239077 : ℕ)^4427*50000000000000^3403 ≤ 17982392140339^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556239077 10000000000 17982392140339 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145817769/5000000000 : ℝ), (4040706089/10000000000 : ℝ), (4556239077/10000000000 : ℝ)] ![(33271701920937/100000000000000 : ℝ), (3076351377839/10000000000000 : ℝ), (17982392140339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145817769/5000000000 : ℝ)|^4427 ≤ (33271701920937/100000000000000 : ℝ)^3403
        have hw : |(2145817769/5000000000 : ℝ)|=(2145817769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4040706089/10000000000 : ℝ)|^4427 ≤ (3076351377839/10000000000000 : ℝ)^3403
        have hw : |(4040706089/10000000000 : ℝ)|=(4040706089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556239077/10000000000 : ℝ)|^4427 ≤ (17982392140339/50000000000000 : ℝ)^3403
        have hw : |(4556239077/10000000000 : ℝ)|=(4556239077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38778423/200000000 : ℝ)*x 0 + (5211136003/10000000000 : ℝ)*x 1 + (2721864787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38778423/200000000 : ℝ)^4427 ≤ (5917648864853/50000000000000 : ℝ)^3403 := by
    have hnat : (38778423 : ℕ)^4427*50000000000000^3403 ≤ 5917648864853^3403*200000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38778423 200000000 5917648864853 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211136003/10000000000 : ℝ)^4427 ≤ (2141530533781/5000000000000 : ℝ)^3403 := by
    have hnat : (5211136003 : ℕ)^4427*5000000000000^3403 ≤ 2141530533781^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211136003 10000000000 2141530533781 5000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721864787/5000000000 : ℝ)^4427 ≤ (45334091589397/100000000000000 : ℝ)^3403 := by
    have hnat : (2721864787 : ℕ)^4427*100000000000000^3403 ≤ 45334091589397^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721864787 5000000000 45334091589397 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38778423/200000000 : ℝ), (5211136003/10000000000 : ℝ), (2721864787/5000000000 : ℝ)] ![(5917648864853/50000000000000 : ℝ), (2141530533781/5000000000000 : ℝ), (45334091589397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38778423/200000000 : ℝ)|^4427 ≤ (5917648864853/50000000000000 : ℝ)^3403
        have hw : |(-38778423/200000000 : ℝ)|=(38778423/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211136003/10000000000 : ℝ)|^4427 ≤ (2141530533781/5000000000000 : ℝ)^3403
        have hw : |(5211136003/10000000000 : ℝ)|=(5211136003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721864787/5000000000 : ℝ)|^4427 ≤ (45334091589397/100000000000000 : ℝ)^3403
        have hw : |(2721864787/5000000000 : ℝ)|=(2721864787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323566429/2500000000 : ℝ)*x 0 + (-91285581/500000000 : ℝ)*x 1 + (2721864869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323566429/2500000000 : ℝ)^4427 ≤ (43721580469593/100000000000000 : ℝ)^3403 := by
    have hnat : (1323566429 : ℕ)^4427*100000000000000^3403 ≤ 43721580469593^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323566429 2500000000 43721580469593 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91285581/500000000 : ℝ)^4427 ≤ (10944326157119/100000000000000 : ℝ)^3403 := by
    have hnat : (91285581 : ℕ)^4427*100000000000000^3403 ≤ 10944326157119^3403*500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91285581 500000000 10944326157119 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721864869/5000000000 : ℝ)^4427 ≤ (45334093366121/100000000000000 : ℝ)^3403 := by
    have hnat : (2721864869 : ℕ)^4427*100000000000000^3403 ≤ 45334093366121^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721864869 5000000000 45334093366121 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323566429/2500000000 : ℝ), (-91285581/500000000 : ℝ), (2721864869/5000000000 : ℝ)] ![(43721580469593/100000000000000 : ℝ), (10944326157119/100000000000000 : ℝ), (45334093366121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323566429/2500000000 : ℝ)|^4427 ≤ (43721580469593/100000000000000 : ℝ)^3403
        have hw : |(1323566429/2500000000 : ℝ)|=(1323566429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91285581/500000000 : ℝ)|^4427 ≤ (10944326157119/100000000000000 : ℝ)^3403
        have hw : |(-91285581/500000000 : ℝ)|=(91285581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721864869/5000000000 : ℝ)|^4427 ≤ (45334093366121/100000000000000 : ℝ)^3403
        have hw : |(2721864869/5000000000 : ℝ)|=(2721864869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647133/5000000 : ℝ)*x 0 + (5443729641/10000000000 : ℝ)*x 1 + (-912855681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647133/5000000 : ℝ)^4427 ≤ (43721583520691/100000000000000 : ℝ)^3403 := by
    have hnat : (2647133 : ℕ)^4427*100000000000000^3403 ≤ 43721583520691^3403*5000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647133 5000000 43721583520691 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443729641/10000000000 : ℝ)^4427 ≤ (22667046157627/50000000000000 : ℝ)^3403 := by
    have hnat : (5443729641 : ℕ)^4427*50000000000000^3403 ≤ 22667046157627^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443729641 10000000000 22667046157627 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912855681/5000000000 : ℝ)^4427 ≤ (10944324145137/100000000000000 : ℝ)^3403 := by
    have hnat : (912855681 : ℕ)^4427*100000000000000^3403 ≤ 10944324145137^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912855681 5000000000 10944324145137 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647133/5000000 : ℝ), (5443729641/10000000000 : ℝ), (-912855681/5000000000 : ℝ)] ![(43721583520691/100000000000000 : ℝ), (22667046157627/50000000000000 : ℝ), (10944324145137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647133/5000000 : ℝ)|^4427 ≤ (43721583520691/100000000000000 : ℝ)^3403
        have hw : |(2647133/5000000 : ℝ)|=(2647133/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443729641/10000000000 : ℝ)|^4427 ≤ (22667046157627/50000000000000 : ℝ)^3403
        have hw : |(5443729641/10000000000 : ℝ)|=(5443729641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912855681/5000000000 : ℝ)|^4427 ≤ (10944324145137/100000000000000 : ℝ)^3403
        have hw : |(-912855681/5000000000 : ℝ)|=(912855681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s3_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291714083/10000000000 : ℝ)*x 0 + (4553486459/10000000000 : ℝ)*x 1 + (2021739729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291714083/10000000000 : ℝ)^4427 ≤ (33272494092953/100000000000000 : ℝ)^3403 := by
    have hnat : (4291714083 : ℕ)^4427*100000000000000^3403 ≤ 33272494092953^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291714083 10000000000 33272494092953 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553486459/10000000000 : ℝ)^4427 ≤ (35936520842579/100000000000000 : ℝ)^3403 := by
    have hnat : (4553486459 : ℕ)^4427*100000000000000^3403 ≤ 35936520842579^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553486459 10000000000 35936520842579 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021739729/5000000000 : ℝ)^4427 ≤ (3848873131107/12500000000000 : ℝ)^3403 := by
    have hnat : (2021739729 : ℕ)^4427*12500000000000^3403 ≤ 3848873131107^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021739729 5000000000 3848873131107 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291714083/10000000000 : ℝ), (4553486459/10000000000 : ℝ), (2021739729/5000000000 : ℝ)] ![(33272494092953/100000000000000 : ℝ), (35936520842579/100000000000000 : ℝ), (3848873131107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291714083/10000000000 : ℝ)|^4427 ≤ (33272494092953/100000000000000 : ℝ)^3403
        have hw : |(4291714083/10000000000 : ℝ)|=(4291714083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553486459/10000000000 : ℝ)|^4427 ≤ (35936520842579/100000000000000 : ℝ)^3403
        have hw : |(4553486459/10000000000 : ℝ)|=(4553486459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021739729/5000000000 : ℝ)|^4427 ≤ (3848873131107/12500000000000 : ℝ)^3403
        have hw : |(2021739729/5000000000 : ℝ)|=(2021739729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10613/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15587/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4051/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (314/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4051/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (314/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4051/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (314/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4051/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (314/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4051/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (314/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4051/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (314/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (314/3125 : ℝ) ^ (4425/1024 : ℝ) ≤ (2435945730691613/50000000000000000000 : ℝ) := by
    have hpowers : (314/3125 : ℝ)^4425 ≤ (2435945730691613/50000000000000000000 : ℝ)^1024 := by
      have hnat : (314 : ℕ)^4425*50000000000000000000^1024 ≤ 2435945730691613^1024*3125^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        314 3125 2435945730691613 50000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (314/3125 : ℝ)) (X := (2435945730691613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4051/25000 : ℝ) ^ (4425/1024 : ℝ) ≤ (38419278680542187/100000000000000000000 : ℝ) := by
    have hpowers : (4051/25000 : ℝ)^4425 ≤ (38419278680542187/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4051 : ℕ)^4425*100000000000000000000^1024 ≤ 38419278680542187^1024*25000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4051 25000 38419278680542187 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4051/25000 : ℝ)) (X := (38419278680542187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002435945730691613/25000000000000000000 : ℝ) ≤ (10000225474805071/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (25002435945730691613/25000000000000000000 : ℝ)^1024 ≤ (10000225474805071/10000000000000000 : ℝ)^4425 := by
      have hnat : (25002435945730691613 : ℕ)^1024*10000000000000000^4425 ≤ 10000225474805071^4425*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002435945730691613 25000000000000000000 10000225474805071 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225474805071/10000000000000000 : ℝ)) (X := (25002435945730691613/25000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043291170141925413/100000000000000000000 : ℝ) ≤ (10001001644861197/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (100043291170141925413/100000000000000000000 : ℝ)^1024 ≤ (10001001644861197/10000000000000000 : ℝ)^4425 := by
      have hnat : (100043291170141925413 : ℕ)^1024*10000000000000000^4425 ≤ 10001001644861197^4425*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043291170141925413 100000000000000000000 10001001644861197 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001001644861197/10000000000000000 : ℝ)) (X := (100043291170141925413/100000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038419278680542187/50000000000000000000 : ℝ) ≤ (10001777814917323/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50038419278680542187/50000000000000000000 : ℝ)^1024 ≤ (10001777814917323/10000000000000000 : ℝ)^4425 := by
      have hnat : (50038419278680542187 : ℕ)^1024*10000000000000000^4425 ≤ 10001777814917323^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038419278680542187 50000000000000000000 10001777814917323 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001777814917323/10000000000000000 : ℝ)) (X := (50038419278680542187/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2435945730691613/50000000000000000000 : ℝ) ≤ ((1025763168490868483/1026000000000000000 : ℝ)+2*(129361676021/102600000000000 : ℝ)*(314/3125 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1025763168490868483/1026000000000000000 : ℝ)+2*(129361676021/102600000000000 : ℝ)*(314/3125 : ℝ)=(10000225474805071/10000000000000000 : ℝ) by norm_num, show 1+2*(2435945730691613/50000000000000000000 : ℝ)=(25002435945730691613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38419278680542187/100000000000000000000 : ℝ)+(2435945730691613/50000000000000000000 : ℝ) ≤ ((1025763168490868483/1026000000000000000 : ℝ)+(129361676021/102600000000000 : ℝ)*((4051/25000 : ℝ)+(314/3125 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (1025763168490868483/1026000000000000000 : ℝ)+(129361676021/102600000000000 : ℝ)*((4051/25000 : ℝ)+(314/3125 : ℝ))=(10001001644861197/10000000000000000 : ℝ) by norm_num, show 1+(38419278680542187/100000000000000000000 : ℝ)+(2435945730691613/50000000000000000000 : ℝ)=(100043291170141925413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38419278680542187/100000000000000000000 : ℝ) ≤ ((1025763168490868483/1026000000000000000 : ℝ)+2*(129361676021/102600000000000 : ℝ)*(4051/25000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1025763168490868483/1026000000000000000 : ℝ)+2*(129361676021/102600000000000 : ℝ)*(4051/25000 : ℝ)=(10001777814917323/10000000000000000 : ℝ) by norm_num, show 1+2*(38419278680542187/100000000000000000000 : ℝ)=(50038419278680542187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1025763168490868483/1026000000000000000 : ℝ)*(X 1 0+X 2 0)+(129361676021/102600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (314/3125 : ℝ)) (hi := (4051/25000 : ℝ)) (c := (1025763168490868483/1026000000000000000 : ℝ)) (alpha := (129361676021/102600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1025763168490868483/1026000000000000000 : ℝ)*(X 0 1+X 2 1)+(129361676021/102600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (314/3125 : ℝ)) (hi := (4051/25000 : ℝ)) (c := (1025763168490868483/1026000000000000000 : ℝ)) (alpha := (129361676021/102600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1025763168490868483/1026000000000000000 : ℝ)*(X 0 2+X 1 2)+(129361676021/102600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (314/3125 : ℝ)) (hi := (4051/25000 : ℝ)) (c := (1025763168490868483/1026000000000000000 : ℝ)) (alpha := (129361676021/102600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1938885159/10000000000 : ℝ)*X 0 0+(680624341/1250000000 : ℝ)*X 0 1+(2604940377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355510719/10000000000 : ℝ)*X 1 0+(-2059560843/10000000000 : ℝ)*X 1 1+(5209880227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071102273/2000000000 : ℝ)*X 2 0+(5209879601/10000000000 : ℝ)*X 2 1+(-2059560811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2145817769/5000000000 : ℝ)*X 0 0+(4040706089/10000000000 : ℝ)*X 0 1+(4556239077/10000000000 : ℝ)*X 0 2+(2145817769/5000000000 : ℝ)*X 1 0+(4040706089/10000000000 : ℝ)*X 1 1+(4556239077/10000000000 : ℝ)*X 1 2+(2145817769/5000000000 : ℝ)*X 2 0+(4040706089/10000000000 : ℝ)*X 2 1+(4556239077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38778423/200000000 : ℝ)*X 0 0+(5211136003/10000000000 : ℝ)*X 0 1+(2721864787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323566429/2500000000 : ℝ)*X 1 0+(-91285581/500000000 : ℝ)*X 1 1+(2721864869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647133/5000000 : ℝ)*X 2 0+(5443729641/10000000000 : ℝ)*X 2 1+(-912855681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4291714083/10000000000 : ℝ)*X 0 0+(4553486459/10000000000 : ℝ)*X 0 1+(2021739729/5000000000 : ℝ)*X 0 2+(4291714083/10000000000 : ℝ)*X 1 0+(4553486459/10000000000 : ℝ)*X 1 1+(2021739729/5000000000 : ℝ)*X 1 2+(4291714083/10000000000 : ℝ)*X 2 0+(4553486459/10000000000 : ℝ)*X 2 1+(2021739729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (653255562652574352836453/56250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444889923/25000000000000 : ℝ)*(base19) + (950914263/50000000000000 : ℝ)*(base23) + (105881819/50000000000000 : ℝ)*(lower2) + (176460301/100000000000000 : ℝ)*(upper3) + (2482209/100000000000000 : ℝ)*(lower4) + (193532865936479/6250000000000 : ℝ)*(major0) + (193532865936479/6250000000000 : ℝ)*(major1) + (193532865936479/6250000000000 : ℝ)*(major2) + (2126637061750107/50000000000000 : ℝ)*(sp0) + (4253291665036191/100000000000000 : ℝ)*(sp1) + (2126645771383679/50000000000000 : ℝ)*(sp2) + (484936708213421/25000000000000 : ℝ)*(sp3) + (1932109567/10000000000000 : ℝ)*(sp4) + (690337709/6250000000000 : ℝ)*(sp7) + (1939757878257029/100000000000000 : ℝ)*(f.failure) + (1063323361148971/25000000000000 : ℝ)*(f.sum) + (3220773049651/1282500000000000000000000000 : ℝ)*base65 + (45563149246593643/6412500000000000000000000000000 : ℝ)*base68 + (40858064466168643/6412500000000000000000000000000 : ℝ)*base70 + (45605903301431143/6412500000000000000000000000000 : ℝ)*base72 + (6835630798637/2565000000000000000000000000 : ℝ)*base73 + (62803400371668857/6412500000000000000000000000000 : ℝ)*base75 + (51355301688093643/6412500000000000000000000000000 : ℝ)*base78 + (31056059658056357/6412500000000000000000000000000 : ℝ)*base79 + (717924456571/1282500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (30255541/5000000000000000000000 : ℝ)*base89 + (30255541/5000000000000000000000 : ℝ)*base91 + (30255541/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (322920732229347670345319/90000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2125709/25000000000000 : ℝ)*(base19) + (12143733/2500000000000 : ℝ)*(base23) + (8223781/100000000000000 : ℝ)*(lower2) + (37191677/50000000000000 : ℝ)*(upper3) + (16531559/20000000000000 : ℝ)*(lower4) + (313005143686967/10000000000000 : ℝ)*(major0) + (313005143686967/10000000000000 : ℝ)*(major1) + (313005143686967/10000000000000 : ℝ)*(major2) + (183300781/2000000000000 : ℝ)*(sp2) + (390072343/100000000000000 : ℝ)*(sp3) + (2149671716385297/50000000000000 : ℝ)*(sp4) + (2149671712133879/50000000000000 : ℝ)*(sp5) + (268708361373889/6250000000000 : ℝ)*(sp6) + (980379465648061/50000000000000 : ℝ)*(sp7) + (122547457585529/6250000000000 : ℝ)*(f.failure) + (2149671716385297/50000000000000 : ℝ)*(f.sum) + (31254994367/27000000000000000000000000 : ℝ)*base66 + (2791172341504681/540000000000000000000000000000 : ℝ)*base68 + (236892386944681/540000000000000000000000000000 : ℝ)*base70 + (283105934755319/540000000000000000000000000000 : ℝ)*base71 + (23040509251/13500000000000000000000000 : ℝ)*base74 + (1200166228864681/540000000000000000000000000000 : ℝ)*base76 + (19692572875319/540000000000000000000000000000 : ℝ)*base77 + (3360453761584681/540000000000000000000000000000 : ℝ)*base80 + (5059677077/2700000000000000000000000 : ℝ)*base82 + (4917959/312500000000000000000 : ℝ)*base90 + (4917959/312500000000000000000 : ℝ)*base92 + (4917959/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1465_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15587/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1465_s4_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-969816313/5000000000 : ℝ)*x 0 + (5440205073/10000000000 : ℝ)*x 1 + (2607089041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969816313/5000000000 : ℝ)^4427 ≤ (2368189552169/20000000000000 : ℝ)^3403 := by
    have hnat : (969816313 : ℕ)^4427*20000000000000^3403 ≤ 2368189552169^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969816313 5000000000 2368189552169 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440205073/10000000000 : ℝ)^4427 ≤ (45295911998343/100000000000000 : ℝ)^3403 := by
    have hnat : (5440205073 : ℕ)^4427*100000000000000^3403 ≤ 45295911998343^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440205073 10000000000 45295911998343 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607089041/5000000000 : ℝ)^4427 ≤ (10715785056439/25000000000000 : ℝ)^3403 := by
    have hnat : (2607089041 : ℕ)^4427*25000000000000^3403 ≤ 10715785056439^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607089041 5000000000 10715785056439 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-969816313/5000000000 : ℝ), (5440205073/10000000000 : ℝ), (2607089041/5000000000 : ℝ)] ![(2368189552169/20000000000000 : ℝ), (45295911998343/100000000000000 : ℝ), (10715785056439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-969816313/5000000000 : ℝ)|^4427 ≤ (2368189552169/20000000000000 : ℝ)^3403
        have hw : |(-969816313/5000000000 : ℝ)|=(969816313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440205073/10000000000 : ℝ)|^4427 ≤ (45295911998343/100000000000000 : ℝ)^3403
        have hw : |(5440205073/10000000000 : ℝ)|=(5440205073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607089041/5000000000 : ℝ)|^4427 ≤ (10715785056439/25000000000000 : ℝ)^3403
        have hw : |(2607089041/5000000000 : ℝ)|=(2607089041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354272041/10000000000 : ℝ)*x 0 + (-2055527819/10000000000 : ℝ)*x 1 + (1303544521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354272041/10000000000 : ℝ)^4427 ≤ (70987748573/160000000000 : ℝ)^3403 := by
    have hnat : (5354272041 : ℕ)^4427*160000000000^3403 ≤ 70987748573^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354272041 10000000000 70987748573 160000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055527819/10000000000 : ℝ)^4427 ≤ (3192379219393/25000000000000 : ℝ)^3403 := by
    have hnat : (2055527819 : ℕ)^4427*25000000000000^3403 ≤ 3192379219393^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055527819 10000000000 3192379219393 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303544521/2500000000 : ℝ)^4427 ≤ (8572628049429/20000000000000 : ℝ)^3403 := by
    have hnat : (1303544521 : ℕ)^4427*20000000000000^3403 ≤ 8572628049429^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303544521 2500000000 8572628049429 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354272041/10000000000 : ℝ), (-2055527819/10000000000 : ℝ), (1303544521/2500000000 : ℝ)] ![(70987748573/160000000000 : ℝ), (3192379219393/25000000000000 : ℝ), (8572628049429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354272041/10000000000 : ℝ)|^4427 ≤ (70987748573/160000000000 : ℝ)^3403
        have hw : |(5354272041/10000000000 : ℝ)|=(5354272041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2055527819/10000000000 : ℝ)|^4427 ≤ (3192379219393/25000000000000 : ℝ)^3403
        have hw : |(-2055527819/10000000000 : ℝ)|=(2055527819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303544521/2500000000 : ℝ)|^4427 ≤ (8572628049429/20000000000000 : ℝ)^3403
        have hw : |(1303544521/2500000000 : ℝ)|=(1303544521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354272027/10000000000 : ℝ)*x 0 + (5214178077/10000000000 : ℝ)*x 1 + (-256940981/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354272027/10000000000 : ℝ)^4427 ≤ (5545917838401/12500000000000 : ℝ)^3403 := by
    have hnat : (5354272027 : ℕ)^4427*12500000000000^3403 ≤ 5545917838401^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354272027 10000000000 5545917838401 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214178077/10000000000 : ℝ)^4427 ≤ (21431570086143/50000000000000 : ℝ)^3403 := by
    have hnat : (5214178077 : ℕ)^4427*50000000000000^3403 ≤ 21431570086143^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214178077 10000000000 21431570086143 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256940981/1250000000 : ℝ)^4427 ≤ (638475855597/5000000000000 : ℝ)^3403 := by
    have hnat : (256940981 : ℕ)^4427*5000000000000^3403 ≤ 638475855597^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256940981 1250000000 638475855597 5000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354272027/10000000000 : ℝ), (5214178077/10000000000 : ℝ), (-256940981/1250000000 : ℝ)] ![(5545917838401/12500000000000 : ℝ), (21431570086143/50000000000000 : ℝ), (638475855597/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354272027/10000000000 : ℝ)|^4427 ≤ (5545917838401/12500000000000 : ℝ)^3403
        have hw : |(5354272027/10000000000 : ℝ)|=(5354272027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214178077/10000000000 : ℝ)|^4427 ≤ (21431570086143/50000000000000 : ℝ)^3403
        have hw : |(5214178077/10000000000 : ℝ)|=(5214178077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256940981/1250000000 : ℝ)|^4427 ≤ (638475855597/5000000000000 : ℝ)^3403
        have hw : |(-256940981/1250000000 : ℝ)|=(256940981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292098781/10000000000 : ℝ)*x 0 + (1012653367/2500000000 : ℝ)*x 1 + (2273110733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292098781/10000000000 : ℝ)^4427 ≤ (8319093514769/25000000000000 : ℝ)^3403 := by
    have hnat : (4292098781 : ℕ)^4427*25000000000000^3403 ≤ 8319093514769^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292098781 10000000000 8319093514769 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012653367/2500000000 : ℝ)^4427 ≤ (6172335233371/20000000000000 : ℝ)^3403 := by
    have hnat : (1012653367 : ℕ)^4427*20000000000000^3403 ≤ 6172335233371^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012653367 2500000000 6172335233371 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273110733/5000000000 : ℝ)^4427 ≤ (17930974879861/50000000000000 : ℝ)^3403 := by
    have hnat : (2273110733 : ℕ)^4427*50000000000000^3403 ≤ 17930974879861^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273110733 5000000000 17930974879861 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292098781/10000000000 : ℝ), (1012653367/2500000000 : ℝ), (2273110733/5000000000 : ℝ)] ![(8319093514769/25000000000000 : ℝ), (6172335233371/20000000000000 : ℝ), (17930974879861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292098781/10000000000 : ℝ)|^4427 ≤ (8319093514769/25000000000000 : ℝ)^3403
        have hw : |(4292098781/10000000000 : ℝ)|=(4292098781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012653367/2500000000 : ℝ)|^4427 ≤ (6172335233371/20000000000000 : ℝ)^3403
        have hw : |(1012653367/2500000000 : ℝ)|=(1012653367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273110733/5000000000 : ℝ)|^4427 ≤ (17930974879861/50000000000000 : ℝ)^3403
        have hw : |(2273110733/5000000000 : ℝ)|=(2273110733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939664341/10000000000 : ℝ)*x 0 + (651917323/1250000000 : ℝ)*x 1 + (2719517983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939664341/10000000000 : ℝ)^4427 ≤ (5920599816553/50000000000000 : ℝ)^3403 := by
    have hnat : (1939664341 : ℕ)^4427*50000000000000^3403 ≤ 5920599816553^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939664341 10000000000 5920599816553 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651917323/1250000000 : ℝ)^4427 ≤ (42875551207403/100000000000000 : ℝ)^3403 := by
    have hnat : (651917323 : ℕ)^4427*100000000000000^3403 ≤ 42875551207403^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651917323 1250000000 42875551207403 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719517983/5000000000 : ℝ)^4427 ≤ (45283249146433/100000000000000 : ℝ)^3403 := by
    have hnat : (2719517983 : ℕ)^4427*100000000000000^3403 ≤ 45283249146433^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719517983 5000000000 45283249146433 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939664341/10000000000 : ℝ), (651917323/1250000000 : ℝ), (2719517983/5000000000 : ℝ)] ![(5920599816553/50000000000000 : ℝ), (42875551207403/100000000000000 : ℝ), (45283249146433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939664341/10000000000 : ℝ)|^4427 ≤ (5920599816553/50000000000000 : ℝ)^3403
        have hw : |(-1939664341/10000000000 : ℝ)|=(1939664341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651917323/1250000000 : ℝ)|^4427 ≤ (42875551207403/100000000000000 : ℝ)^3403
        have hw : |(651917323/1250000000 : ℝ)|=(651917323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719517983/5000000000 : ℝ)|^4427 ≤ (45283249146433/100000000000000 : ℝ)^3403
        have hw : |(2719517983/5000000000 : ℝ)|=(2719517983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295397321/10000000000 : ℝ)*x 0 + (-28604221/156250000 : ℝ)*x 1 + (5439036187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295397321/10000000000 : ℝ)^4427 ≤ (8746747606437/20000000000000 : ℝ)^3403 := by
    have hnat : (5295397321 : ℕ)^4427*20000000000000^3403 ≤ 8746747606437^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295397321 10000000000 8746747606437 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28604221/156250000 : ℝ)^4427 ≤ (2745752601229/25000000000000 : ℝ)^3403 := by
    have hnat : (28604221 : ℕ)^4427*25000000000000^3403 ≤ 2745752601229^3403*156250000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28604221 156250000 2745752601229 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439036187/10000000000 : ℝ)^4427 ≤ (9056650308011/20000000000000 : ℝ)^3403 := by
    have hnat : (5439036187 : ℕ)^4427*20000000000000^3403 ≤ 9056650308011^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439036187 10000000000 9056650308011 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295397321/10000000000 : ℝ), (-28604221/156250000 : ℝ), (5439036187/10000000000 : ℝ)] ![(8746747606437/20000000000000 : ℝ), (2745752601229/25000000000000 : ℝ), (9056650308011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295397321/10000000000 : ℝ)|^4427 ≤ (8746747606437/20000000000000 : ℝ)^3403
        have hw : |(5295397321/10000000000 : ℝ)|=(5295397321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28604221/156250000 : ℝ)|^4427 ≤ (2745752601229/25000000000000 : ℝ)^3403
        have hw : |(-28604221/156250000 : ℝ)|=(28604221/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439036187/10000000000 : ℝ)|^4427 ≤ (9056650308011/20000000000000 : ℝ)^3403
        have hw : |(5439036187/10000000000 : ℝ)|=(5439036187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295398619/10000000000 : ℝ)*x 0 + (1359758791/2500000000 : ℝ)*x 1 + (-915334889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295398619/10000000000 : ℝ)^4427 ≤ (8746750395577/20000000000000 : ℝ)^3403 := by
    have hnat : (5295398619 : ℕ)^4427*20000000000000^3403 ≤ 8746750395577^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295398619 10000000000 8746750395577 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359758791/2500000000 : ℝ)^4427 ≤ (22641620230039/50000000000000 : ℝ)^3403 := by
    have hnat : (1359758791 : ℕ)^4427*50000000000000^3403 ≤ 22641620230039^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359758791 2500000000 22641620230039 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (915334889/5000000000 : ℝ)^4427 ≤ (5491503774189/50000000000000 : ℝ)^3403 := by
    have hnat : (915334889 : ℕ)^4427*50000000000000^3403 ≤ 5491503774189^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915334889 5000000000 5491503774189 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295398619/10000000000 : ℝ), (1359758791/2500000000 : ℝ), (-915334889/5000000000 : ℝ)] ![(8746750395577/20000000000000 : ℝ), (22641620230039/50000000000000 : ℝ), (5491503774189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295398619/10000000000 : ℝ)|^4427 ≤ (8746750395577/20000000000000 : ℝ)^3403
        have hw : |(5295398619/10000000000 : ℝ)|=(5295398619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359758791/2500000000 : ℝ)|^4427 ≤ (22641620230039/50000000000000 : ℝ)^3403
        have hw : |(1359758791/2500000000 : ℝ)|=(1359758791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-915334889/5000000000 : ℝ)|^4427 ≤ (5491503774189/50000000000000 : ℝ)^3403
        have hw : |(-915334889/5000000000 : ℝ)|=(915334889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s4_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146084263/5000000000 : ℝ)*x 0 + (4543676421/10000000000 : ℝ)*x 1 + (1013294257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146084263/5000000000 : ℝ)^4427 ≤ (16638538750301/50000000000000 : ℝ)^3403 := by
    have hnat : (2146084263 : ℕ)^4427*50000000000000^3403 ≤ 16638538750301^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146084263 5000000000 16638538750301 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543676421/10000000000 : ℝ)^4427 ≤ (35835834775827/100000000000000 : ℝ)^3403 := by
    have hnat : (4543676421 : ℕ)^4427*100000000000000^3403 ≤ 35835834775827^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543676421 10000000000 35835834775827 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013294257/2500000000 : ℝ)^4427 ≤ (6177417542863/20000000000000 : ℝ)^3403 := by
    have hnat : (1013294257 : ℕ)^4427*20000000000000^3403 ≤ 6177417542863^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013294257 2500000000 6177417542863 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146084263/5000000000 : ℝ), (4543676421/10000000000 : ℝ), (1013294257/2500000000 : ℝ)] ![(16638538750301/50000000000000 : ℝ), (35835834775827/100000000000000 : ℝ), (6177417542863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146084263/5000000000 : ℝ)|^4427 ≤ (16638538750301/50000000000000 : ℝ)^3403
        have hw : |(2146084263/5000000000 : ℝ)|=(2146084263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543676421/10000000000 : ℝ)|^4427 ≤ (35835834775827/100000000000000 : ℝ)^3403
        have hw : |(4543676421/10000000000 : ℝ)|=(4543676421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013294257/2500000000 : ℝ)|^4427 ≤ (6177417542863/20000000000000 : ℝ)^3403
        have hw : |(1013294257/2500000000 : ℝ)|=(1013294257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2141/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10613/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (6171135949466681/100000000000000000000 : ℝ) := by
    have hpowers : (10613/100000 : ℝ)^4425 ≤ (6171135949466681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10613 : ℕ)^4425*100000000000000000000^1024 ≤ 6171135949466681^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10613 100000 6171135949466681 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10613/100000 : ℝ)) (X := (6171135949466681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15587/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (6497160107365019/20000000000000000000 : ℝ) := by
    have hpowers : (15587/100000 : ℝ)^4425 ≤ (6497160107365019/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15587 : ℕ)^4425*20000000000000000000^1024 ≤ 6497160107365019^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15587 100000 6497160107365019 20000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15587/100000 : ℝ)) (X := (6497160107365019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006171135949466681/50000000000000000000 : ℝ) ≤ (5000142800983247/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50006171135949466681/50000000000000000000 : ℝ)^1024 ≤ (5000142800983247/5000000000000000 : ℝ)^4425 := by
      have hnat : (50006171135949466681 : ℕ)^1024*5000000000000000^4425 ≤ 5000142800983247^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006171135949466681 50000000000000000000 5000142800983247 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000142800983247/5000000000000000 : ℝ)) (X := (50006171135949466681/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563104014632598309/1562500000000000000 : ℝ) ≤ (5000447218347441/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (1563104014632598309/1562500000000000000 : ℝ)^1024 ≤ (5000447218347441/5000000000000000 : ℝ)^4425 := by
      have hnat : (1563104014632598309 : ℕ)^1024*5000000000000000^4425 ≤ 5000447218347441^4425*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563104014632598309 1562500000000000000 5000447218347441 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000447218347441/5000000000000000 : ℝ)) (X := (1563104014632598309/1562500000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006497160107365019/10000000000000000000 : ℝ) ≤ (1000150327142327/1000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (10006497160107365019/10000000000000000000 : ℝ)^1024 ≤ (1000150327142327/1000000000000000 : ℝ)^4425 := by
      have hnat : (10006497160107365019 : ℕ)^1024*1000000000000000^4425 ≤ 1000150327142327^4425*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006497160107365019 10000000000000000000 1000150327142327 1000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000150327142327/1000000000000000 : ℝ)) (X := (10006497160107365019/10000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6171135949466681/100000000000000000000 : ℝ) ≤ ((12432124364559144367/12435000000000000000 : ℝ)+2*(152208682097/124350000000000 : ℝ)*(10613/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (12432124364559144367/12435000000000000000 : ℝ)+2*(152208682097/124350000000000 : ℝ)*(10613/100000 : ℝ)=(5000142800983247/5000000000000000 : ℝ) by norm_num, show 1+2*(6171135949466681/100000000000000000000 : ℝ)=(50006171135949466681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6497160107365019/20000000000000000000 : ℝ)+(6171135949466681/100000000000000000000 : ℝ) ≤ ((12432124364559144367/12435000000000000000 : ℝ)+(152208682097/124350000000000 : ℝ)*((15587/100000 : ℝ)+(10613/100000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (12432124364559144367/12435000000000000000 : ℝ)+(152208682097/124350000000000 : ℝ)*((15587/100000 : ℝ)+(10613/100000 : ℝ))=(5000447218347441/5000000000000000 : ℝ) by norm_num, show 1+(6497160107365019/20000000000000000000 : ℝ)+(6171135949466681/100000000000000000000 : ℝ)=(1563104014632598309/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6497160107365019/20000000000000000000 : ℝ) ≤ ((12432124364559144367/12435000000000000000 : ℝ)+2*(152208682097/124350000000000 : ℝ)*(15587/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (12432124364559144367/12435000000000000000 : ℝ)+2*(152208682097/124350000000000 : ℝ)*(15587/100000 : ℝ)=(1000150327142327/1000000000000000 : ℝ) by norm_num, show 1+2*(6497160107365019/20000000000000000000 : ℝ)=(10006497160107365019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12432124364559144367/12435000000000000000 : ℝ)*(X 1 0+X 2 0)+(152208682097/124350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (15587/100000 : ℝ)) (c := (12432124364559144367/12435000000000000000 : ℝ)) (alpha := (152208682097/124350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12432124364559144367/12435000000000000000 : ℝ)*(X 0 1+X 2 1)+(152208682097/124350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (15587/100000 : ℝ)) (c := (12432124364559144367/12435000000000000000 : ℝ)) (alpha := (152208682097/124350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12432124364559144367/12435000000000000000 : ℝ)*(X 0 2+X 1 2)+(152208682097/124350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (15587/100000 : ℝ)) (c := (12432124364559144367/12435000000000000000 : ℝ)) (alpha := (152208682097/124350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-969816313/5000000000 : ℝ)*X 0 0+(5440205073/10000000000 : ℝ)*X 0 1+(2607089041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354272041/10000000000 : ℝ)*X 1 0+(-2055527819/10000000000 : ℝ)*X 1 1+(1303544521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354272027/10000000000 : ℝ)*X 2 0+(5214178077/10000000000 : ℝ)*X 2 1+(-256940981/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4292098781/10000000000 : ℝ)*X 0 0+(1012653367/2500000000 : ℝ)*X 0 1+(2273110733/5000000000 : ℝ)*X 0 2+(4292098781/10000000000 : ℝ)*X 1 0+(1012653367/2500000000 : ℝ)*X 1 1+(2273110733/5000000000 : ℝ)*X 1 2+(4292098781/10000000000 : ℝ)*X 2 0+(1012653367/2500000000 : ℝ)*X 2 1+(2273110733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1939664341/10000000000 : ℝ)*X 0 0+(651917323/1250000000 : ℝ)*X 0 1+(2719517983/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295397321/10000000000 : ℝ)*X 1 0+(-28604221/156250000 : ℝ)*X 1 1+(5439036187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295398619/10000000000 : ℝ)*X 2 0+(1359758791/2500000000 : ℝ)*X 2 1+(-915334889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146084263/5000000000 : ℝ)*X 0 0+(4543676421/10000000000 : ℝ)*X 0 1+(1013294257/2500000000 : ℝ)*X 0 2+(2146084263/5000000000 : ℝ)*X 1 0+(4543676421/10000000000 : ℝ)*X 1 1+(1013294257/2500000000 : ℝ)*X 1 2+(2146084263/5000000000 : ℝ)*X 2 0+(4543676421/10000000000 : ℝ)*X 2 1+(1013294257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1172475634656703728791384839/103625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (504955553/25000000000000 : ℝ)*(base19) + (1899737521/100000000000000 : ℝ)*(base23) + (3631411/6250000000000 : ℝ)*(lower2) + (294990887/100000000000000 : ℝ)*(upper3) + (93051681/50000000000000 : ℝ)*(upper5) + (3221032519088183/100000000000000 : ℝ)*(major0) + (3221032519088183/100000000000000 : ℝ)*(major1) + (3221032519088183/100000000000000 : ℝ)*(major2) + (110607052891743/2500000000000 : ℝ)*(sp0) + (276519375351529/6250000000000 : ℝ)*(sp1) + (2212155062854577/50000000000000 : ℝ)*(sp2) + (1008868682762703/50000000000000 : ℝ)*(sp3) + (5981955391/20000000000000 : ℝ)*(sp4) + (122160407/800000000000 : ℝ)*(sp7) + (1008876317788141/50000000000000 : ℝ)*(f.failure) + (1106078006361669/25000000000000 : ℝ)*(f.sum) + (4055613564467/12435000000000000000000000000 : ℝ)*base65 + (227108032178438387/414500000000000000000000000000000 : ℝ)*base67 + (5613992475734938387/414500000000000000000000000000000 : ℝ)*base69 + (676540805228061613/414500000000000000000000000000000 : ℝ)*base72 + (38810049914143/12435000000000000000000000000 : ℝ)*base74 + (1110447320447938387/414500000000000000000000000000000 : ℝ)*base75 + (791110791228938387/414500000000000000000000000000000 : ℝ)*base77 + (607206365097438387/414500000000000000000000000000000 : ℝ)*base79 + (37530974393131/6217500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (27495389/2500000000000000000000 : ℝ)*base89 + (27495389/2500000000000000000000 : ℝ)*base91 + (27495389/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (967560979331602283457857457/103625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1533558977/100000000000000 : ℝ)*(base19) + (585137773/20000000000000 : ℝ)*(base23) + (6565797/3125000000000 : ℝ)*(upper3) + (21671659/25000000000000 : ℝ)*(lower4) + (269616149/100000000000000 : ℝ)*(upper5) + (1627268095975757/50000000000000 : ℝ)*(major0) + (1627268095975757/50000000000000 : ℝ)*(major1) + (1627268095975757/50000000000000 : ℝ)*(major2) + (26156029893/100000000000000 : ℝ)*(sp1) + (38089466143/100000000000000 : ℝ)*(sp2) + (2235165859227411/50000000000000 : ℝ)*(sp4) + (139697000902061/3125000000000 : ℝ)*(sp5) + (894058140659963/20000000000000 : ℝ)*(sp6) + (1019370177105123/50000000000000 : ℝ)*(sp7) + (1019370177105123/50000000000000 : ℝ)*(f.failure) + (2235165859227411/50000000000000 : ℝ)*(f.sum) + (41892502087/6217500000000000000000000000 : ℝ)*base66 + (1293549952788829727/207250000000000000000000000000000 : ℝ)*base68 + (3062344834102329727/207250000000000000000000000000000 : ℝ)*base70 + (511697667094579727/207250000000000000000000000000000 : ℝ)*base72 + (13142574555569/12435000000000000000000000000 : ℝ)*base74 + (4145338410286329727/207250000000000000000000000000000 : ℝ)*base76 + (1212907553566829727/207250000000000000000000000000000 : ℝ)*base78 + (4204705652155579727/207250000000000000000000000000000 : ℝ)*base80 + (24733279022137/6217500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (20076467/2500000000000000000000 : ℝ)*base89 + (20076467/2500000000000000000000 : ℝ)*base91 + (20076467/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1465_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1465_s5_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939737083/10000000000 : ℝ)*x 0 + (2719759137/5000000000 : ℝ)*x 1 + (521479611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939737083/10000000000 : ℝ)^4427 ≤ (5920888667893/50000000000000 : ℝ)^3403 := by
    have hnat : (1939737083 : ℕ)^4427*50000000000000^3403 ≤ 5920888667893^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939737083 10000000000 5920888667893 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719759137/5000000000 : ℝ)^4427 ≤ (5661059128741/12500000000000 : ℝ)^3403 := by
    have hnat : (2719759137 : ℕ)^4427*12500000000000^3403 ≤ 5661059128741^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719759137 5000000000 5661059128741 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521479611/1000000000 : ℝ)^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403 := by
    have hnat : (521479611 : ℕ)^4427*100000000000000^3403 ≤ 42869749619031^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521479611 1000000000 42869749619031 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939737083/10000000000 : ℝ), (2719759137/5000000000 : ℝ), (521479611/1000000000 : ℝ)] ![(5920888667893/50000000000000 : ℝ), (5661059128741/12500000000000 : ℝ), (42869749619031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939737083/10000000000 : ℝ)|^4427 ≤ (5920888667893/50000000000000 : ℝ)^3403
        have hw : |(-1939737083/10000000000 : ℝ)|=(1939737083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719759137/5000000000 : ℝ)|^4427 ≤ (5661059128741/12500000000000 : ℝ)^3403
        have hw : |(2719759137/5000000000 : ℝ)|=(2719759137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521479611/1000000000 : ℝ)|^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403
        have hw : |(521479611/1000000000 : ℝ)|=(521479611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677047273/5000000000 : ℝ)*x 0 + (-2054946721/10000000000 : ℝ)*x 1 + (521479611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677047273/5000000000 : ℝ)^4427 ≤ (44365429507701/100000000000000 : ℝ)^3403 := by
    have hnat : (2677047273 : ℕ)^4427*100000000000000^3403 ≤ 44365429507701^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677047273 5000000000 44365429507701 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054946721/10000000000 : ℝ)^4427 ≤ (12764820861361/100000000000000 : ℝ)^3403 := by
    have hnat : (2054946721 : ℕ)^4427*100000000000000^3403 ≤ 12764820861361^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054946721 10000000000 12764820861361 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521479611/1000000000 : ℝ)^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403 := by
    have hnat : (521479611 : ℕ)^4427*100000000000000^3403 ≤ 42869749619031^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521479611 1000000000 42869749619031 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677047273/5000000000 : ℝ), (-2054946721/10000000000 : ℝ), (521479611/1000000000 : ℝ)] ![(44365429507701/100000000000000 : ℝ), (12764820861361/100000000000000 : ℝ), (42869749619031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677047273/5000000000 : ℝ)|^4427 ≤ (44365429507701/100000000000000 : ℝ)^3403
        have hw : |(2677047273/5000000000 : ℝ)|=(2677047273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054946721/10000000000 : ℝ)|^4427 ≤ (12764820861361/100000000000000 : ℝ)^3403
        have hw : |(-2054946721/10000000000 : ℝ)|=(2054946721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521479611/1000000000 : ℝ)|^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403
        have hw : |(521479611/1000000000 : ℝ)|=(521479611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677047273/5000000000 : ℝ)*x 0 + (521479611/1000000000 : ℝ)*x 1 + (-2054946721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677047273/5000000000 : ℝ)^4427 ≤ (44365429507701/100000000000000 : ℝ)^3403 := by
    have hnat : (2677047273 : ℕ)^4427*100000000000000^3403 ≤ 44365429507701^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677047273 5000000000 44365429507701 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521479611/1000000000 : ℝ)^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403 := by
    have hnat : (521479611 : ℕ)^4427*100000000000000^3403 ≤ 42869749619031^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521479611 1000000000 42869749619031 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054946721/10000000000 : ℝ)^4427 ≤ (12764820861361/100000000000000 : ℝ)^3403 := by
    have hnat : (2054946721 : ℕ)^4427*100000000000000^3403 ≤ 12764820861361^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054946721 10000000000 12764820861361 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677047273/5000000000 : ℝ), (521479611/1000000000 : ℝ), (-2054946721/10000000000 : ℝ)] ![(44365429507701/100000000000000 : ℝ), (42869749619031/100000000000000 : ℝ), (12764820861361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677047273/5000000000 : ℝ)|^4427 ≤ (44365429507701/100000000000000 : ℝ)^3403
        have hw : |(2677047273/5000000000 : ℝ)|=(2677047273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521479611/1000000000 : ℝ)|^4427 ≤ (42869749619031/100000000000000 : ℝ)^3403
        have hw : |(521479611/1000000000 : ℝ)|=(521479611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054946721/10000000000 : ℝ)|^4427 ≤ (12764820861361/100000000000000 : ℝ)^3403
        have hw : |(-2054946721/10000000000 : ℝ)|=(2054946721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073040937/2500000000 : ℝ)*x 0 + (2026018191/5000000000 : ℝ)*x 1 + (4544783133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073040937/2500000000 : ℝ)^4427 ≤ (2079814331877/6250000000000 : ℝ)^3403 := by
    have hnat : (1073040937 : ℕ)^4427*6250000000000^3403 ≤ 2079814331877^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073040937 2500000000 2079814331877 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026018191/5000000000 : ℝ)^4427 ≤ (30875780348219/100000000000000 : ℝ)^3403 := by
    have hnat : (2026018191 : ℕ)^4427*100000000000000^3403 ≤ 30875780348219^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026018191 5000000000 30875780348219 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4544783133/10000000000 : ℝ)^4427 ≤ (35847190327459/100000000000000 : ℝ)^3403 := by
    have hnat : (4544783133 : ℕ)^4427*100000000000000^3403 ≤ 35847190327459^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544783133 10000000000 35847190327459 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073040937/2500000000 : ℝ), (2026018191/5000000000 : ℝ), (4544783133/10000000000 : ℝ)] ![(2079814331877/6250000000000 : ℝ), (30875780348219/100000000000000 : ℝ), (35847190327459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073040937/2500000000 : ℝ)|^4427 ≤ (2079814331877/6250000000000 : ℝ)^3403
        have hw : |(1073040937/2500000000 : ℝ)|=(1073040937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2026018191/5000000000 : ℝ)|^4427 ≤ (30875780348219/100000000000000 : ℝ)^3403
        have hw : |(2026018191/5000000000 : ℝ)|=(2026018191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4544783133/10000000000 : ℝ)|^4427 ≤ (35847190327459/100000000000000 : ℝ)^3403
        have hw : |(4544783133/10000000000 : ℝ)|=(4544783133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-387953641/2000000000 : ℝ)*x 0 + (2607971727/5000000000 : ℝ)*x 1 + (543836251/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387953641/2000000000 : ℝ)^4427 ≤ (1184202450259/10000000000000 : ℝ)^3403 := by
    have hnat : (387953641 : ℕ)^4427*10000000000000^3403 ≤ 1184202450259^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387953641 2000000000 1184202450259 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607971727/5000000000 : ℝ)^4427 ≤ (21441010157719/50000000000000 : ℝ)^3403 := by
    have hnat : (2607971727 : ℕ)^4427*50000000000000^3403 ≤ 21441010157719^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607971727 5000000000 21441010157719 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543836251/1000000000 : ℝ)^4427 ≤ (22637977584977/50000000000000 : ℝ)^3403 := by
    have hnat : (543836251 : ℕ)^4427*50000000000000^3403 ≤ 22637977584977^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543836251 1000000000 22637977584977 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387953641/2000000000 : ℝ), (2607971727/5000000000 : ℝ), (543836251/1000000000 : ℝ)] ![(1184202450259/10000000000000 : ℝ), (21441010157719/50000000000000 : ℝ), (22637977584977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387953641/2000000000 : ℝ)|^4427 ≤ (1184202450259/10000000000000 : ℝ)^3403
        have hw : |(-387953641/2000000000 : ℝ)|=(387953641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607971727/5000000000 : ℝ)|^4427 ≤ (21441010157719/50000000000000 : ℝ)^3403
        have hw : |(2607971727/5000000000 : ℝ)|=(2607971727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543836251/1000000000 : ℝ)|^4427 ≤ (22637977584977/50000000000000 : ℝ)^3403
        have hw : |(543836251/1000000000 : ℝ)|=(543836251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647780259/5000000000 : ℝ)*x 0 + (-915690161/5000000000 : ℝ)*x 1 + (435069/800000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647780259/5000000000 : ℝ)^4427 ≤ (43735491427353/100000000000000 : ℝ)^3403 := by
    have hnat : (2647780259 : ℕ)^4427*100000000000000^3403 ≤ 43735491427353^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647780259 5000000000 43735491427353 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915690161/5000000000 : ℝ)^4427 ≤ (274713837213/2500000000000 : ℝ)^3403 := by
    have hnat : (915690161 : ℕ)^4427*2500000000000^3403 ≤ 274713837213^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915690161 5000000000 274713837213 2500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435069/800000 : ℝ)^4427 ≤ (45275955061649/100000000000000 : ℝ)^3403 := by
    have hnat : (435069 : ℕ)^4427*100000000000000^3403 ≤ 45275955061649^3403*800000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435069 800000 45275955061649 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647780259/5000000000 : ℝ), (-915690161/5000000000 : ℝ), (435069/800000 : ℝ)] ![(43735491427353/100000000000000 : ℝ), (274713837213/2500000000000 : ℝ), (45275955061649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647780259/5000000000 : ℝ)|^4427 ≤ (43735491427353/100000000000000 : ℝ)^3403
        have hw : |(2647780259/5000000000 : ℝ)|=(2647780259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-915690161/5000000000 : ℝ)|^4427 ≤ (274713837213/2500000000000 : ℝ)^3403
        have hw : |(-915690161/5000000000 : ℝ)|=(915690161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(435069/800000 : ℝ)|^4427 ≤ (45275955061649/100000000000000 : ℝ)^3403
        have hw : |(435069/800000 : ℝ)|=(435069/800000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647780251/5000000000 : ℝ)*x 0 + (5438362509/10000000000 : ℝ)*x 1 + (-457845083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647780251/5000000000 : ℝ)^4427 ≤ (43735491255447/100000000000000 : ℝ)^3403 := by
    have hnat : (2647780251 : ℕ)^4427*100000000000000^3403 ≤ 43735491255447^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647780251 5000000000 43735491255447 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438362509/10000000000 : ℝ)^4427 ≤ (11318988789781/25000000000000 : ℝ)^3403 := by
    have hnat : (5438362509 : ℕ)^4427*25000000000000^3403 ≤ 11318988789781^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438362509 10000000000 11318988789781 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457845083/2500000000 : ℝ)^4427 ≤ (10988553566577/100000000000000 : ℝ)^3403 := by
    have hnat : (457845083 : ℕ)^4427*100000000000000^3403 ≤ 10988553566577^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457845083 2500000000 10988553566577 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647780251/5000000000 : ℝ), (5438362509/10000000000 : ℝ), (-457845083/2500000000 : ℝ)] ![(43735491255447/100000000000000 : ℝ), (11318988789781/25000000000000 : ℝ), (10988553566577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647780251/5000000000 : ℝ)|^4427 ≤ (43735491255447/100000000000000 : ℝ)^3403
        have hw : |(2647780251/5000000000 : ℝ)|=(2647780251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438362509/10000000000 : ℝ)|^4427 ≤ (11318988789781/25000000000000 : ℝ)^3403
        have hw : |(5438362509/10000000000 : ℝ)|=(5438362509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457845083/2500000000 : ℝ)|^4427 ≤ (10988553566577/100000000000000 : ℝ)^3403
        have hw : |(-457845083/2500000000 : ℝ)|=(457845083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s5_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146116009/5000000000 : ℝ)*x 0 + (4542267369/10000000000 : ℝ)*x 1 + (2027285311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146116009/5000000000 : ℝ)^4427 ≤ (33277717877947/100000000000000 : ℝ)^3403 := by
    have hnat : (2146116009 : ℕ)^4427*100000000000000^3403 ≤ 33277717877947^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146116009 5000000000 33277717877947 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542267369/10000000000 : ℝ)^4427 ≤ (2238836139539/6250000000000 : ℝ)^3403 := by
    have hnat : (4542267369 : ℕ)^4427*6250000000000^3403 ≤ 2238836139539^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542267369 10000000000 2238836139539 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027285311/5000000000 : ℝ)^4427 ≤ (15450451942559/50000000000000 : ℝ)^3403 := by
    have hnat : (2027285311 : ℕ)^4427*50000000000000^3403 ≤ 15450451942559^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027285311 5000000000 15450451942559 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146116009/5000000000 : ℝ), (4542267369/10000000000 : ℝ), (2027285311/5000000000 : ℝ)] ![(33277717877947/100000000000000 : ℝ), (2238836139539/6250000000000 : ℝ), (15450451942559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146116009/5000000000 : ℝ)|^4427 ≤ (33277717877947/100000000000000 : ℝ)^3403
        have hw : |(2146116009/5000000000 : ℝ)|=(2146116009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542267369/10000000000 : ℝ)|^4427 ≤ (2238836139539/6250000000000 : ℝ)^3403
        have hw : |(4542267369/10000000000 : ℝ)|=(4542267369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2027285311/5000000000 : ℝ)|^4427 ≤ (15450451942559/50000000000000 : ℝ)^3403
        have hw : |(2027285311/5000000000 : ℝ)|=(2027285311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10719/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2141/20000 : ℝ) ^ (4425/1024 : ℝ) ≤ (1601413578809177/25000000000000000000 : ℝ) := by
    have hpowers : (2141/20000 : ℝ)^4425 ≤ (1601413578809177/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2141 : ℕ)^4425*25000000000000000000^1024 ≤ 1601413578809177^1024*20000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2141 20000 1601413578809177 25000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2141/20000 : ℝ)) (X := (1601413578809177/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4425/1024 : ℝ) ≤ (31603539282746081/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4425 ≤ (31603539282746081/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4425*100000000000000000000^1024 ≤ 31603539282746081^1024*3125^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 31603539282746081 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (31603539282746081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501601413578809177/12500000000000000000 : ℝ) ≤ (5000148227505183/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (12501601413578809177/12500000000000000000 : ℝ)^1024 ≤ (5000148227505183/5000000000000000 : ℝ)^4425 := by
      have hnat : (12501601413578809177 : ℕ)^1024*5000000000000000^4425 ≤ 5000148227505183^4425*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501601413578809177 12500000000000000000 5000148227505183 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000148227505183/5000000000000000 : ℝ)) (X := (12501601413578809177/12500000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038009193597982789/100000000000000000000 : ℝ) ≤ (5000439725767061/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (100038009193597982789/100000000000000000000 : ℝ)^1024 ≤ (5000439725767061/5000000000000000 : ℝ)^4425 := by
      have hnat : (100038009193597982789 : ℕ)^1024*5000000000000000^4425 ≤ 5000439725767061^4425*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038009193597982789 100000000000000000000 5000439725767061 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000439725767061/5000000000000000 : ℝ)) (X := (100038009193597982789/100000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031603539282746081/50000000000000000000 : ℝ) ≤ (5000731224028939/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50031603539282746081/50000000000000000000 : ℝ)^1024 ≤ (5000731224028939/5000000000000000 : ℝ)^4425 := by
      have hnat : (50031603539282746081 : ℕ)^1024*5000000000000000^4425 ≤ 5000731224028939^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031603539282746081 50000000000000000000 5000731224028939 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000731224028939/5000000000000000 : ℝ)) (X := (50031603539282746081/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1601413578809177/25000000000000000000 : ℝ) ≤ ((23909467994370482309/23915000000000000000 : ℝ)+2*(145749130939/119575000000000 : ℝ)*(2141/20000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (23909467994370482309/23915000000000000000 : ℝ)+2*(145749130939/119575000000000 : ℝ)*(2141/20000 : ℝ)=(5000148227505183/5000000000000000 : ℝ) by norm_num, show 1+2*(1601413578809177/25000000000000000000 : ℝ)=(12501601413578809177/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31603539282746081/100000000000000000000 : ℝ)+(1601413578809177/25000000000000000000 : ℝ) ≤ ((23909467994370482309/23915000000000000000 : ℝ)+(145749130939/119575000000000 : ℝ)*((484/3125 : ℝ)+(2141/20000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (23909467994370482309/23915000000000000000 : ℝ)+(145749130939/119575000000000 : ℝ)*((484/3125 : ℝ)+(2141/20000 : ℝ))=(5000439725767061/5000000000000000 : ℝ) by norm_num, show 1+(31603539282746081/100000000000000000000 : ℝ)+(1601413578809177/25000000000000000000 : ℝ)=(100038009193597982789/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31603539282746081/100000000000000000000 : ℝ) ≤ ((23909467994370482309/23915000000000000000 : ℝ)+2*(145749130939/119575000000000 : ℝ)*(484/3125 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (23909467994370482309/23915000000000000000 : ℝ)+2*(145749130939/119575000000000 : ℝ)*(484/3125 : ℝ)=(5000731224028939/5000000000000000 : ℝ) by norm_num, show 1+2*(31603539282746081/100000000000000000000 : ℝ)=(50031603539282746081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23909467994370482309/23915000000000000000 : ℝ)*(X 1 0+X 2 0)+(145749130939/119575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23909467994370482309/23915000000000000000 : ℝ)) (alpha := (145749130939/119575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23909467994370482309/23915000000000000000 : ℝ)*(X 0 1+X 2 1)+(145749130939/119575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23909467994370482309/23915000000000000000 : ℝ)) (alpha := (145749130939/119575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23909467994370482309/23915000000000000000 : ℝ)*(X 0 2+X 1 2)+(145749130939/119575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23909467994370482309/23915000000000000000 : ℝ)) (alpha := (145749130939/119575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1939737083/10000000000 : ℝ)*X 0 0+(2719759137/5000000000 : ℝ)*X 0 1+(521479611/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677047273/5000000000 : ℝ)*X 1 0+(-2054946721/10000000000 : ℝ)*X 1 1+(521479611/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677047273/5000000000 : ℝ)*X 2 0+(521479611/1000000000 : ℝ)*X 2 1+(-2054946721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073040937/2500000000 : ℝ)*X 0 0+(2026018191/5000000000 : ℝ)*X 0 1+(4544783133/10000000000 : ℝ)*X 0 2+(1073040937/2500000000 : ℝ)*X 1 0+(2026018191/5000000000 : ℝ)*X 1 1+(4544783133/10000000000 : ℝ)*X 1 2+(1073040937/2500000000 : ℝ)*X 2 0+(2026018191/5000000000 : ℝ)*X 2 1+(4544783133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-387953641/2000000000 : ℝ)*X 0 0+(2607971727/5000000000 : ℝ)*X 0 1+(543836251/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647780259/5000000000 : ℝ)*X 1 0+(-915690161/5000000000 : ℝ)*X 1 1+(435069/800000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647780251/5000000000 : ℝ)*X 2 0+(5438362509/10000000000 : ℝ)*X 2 1+(-457845083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146116009/5000000000 : ℝ)*X 0 0+(4542267369/10000000000 : ℝ)*X 0 1+(2027285311/5000000000 : ℝ)*X 0 2+(2146116009/5000000000 : ℝ)*X 1 0+(4542267369/10000000000 : ℝ)*X 1 1+(2027285311/5000000000 : ℝ)*X 1 2+(2146116009/5000000000 : ℝ)*X 2 0+(4542267369/10000000000 : ℝ)*X 2 1+(2027285311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43497555179498206084329/11957500000000000000000000000 : ℝ) := by norm_num
    linear_combination (165017913/25000000000000 : ℝ)*(base19) + (154001521/25000000000000 : ℝ)*(base23) + (11796561/50000000000000 : ℝ)*(lower2) + (91601601/100000000000000 : ℝ)*(upper3) + (2946237/5000000000000 : ℝ)*(upper5) + (1619852350425691/50000000000000 : ℝ)*(major0) + (1619852350425691/50000000000000 : ℝ)*(major1) + (1619852350425691/50000000000000 : ℝ)*(major2) + (1112487448009889/25000000000000 : ℝ)*(sp0) + (4449959162819733/100000000000000 : ℝ)*(sp1) + (4449959206885301/100000000000000 : ℝ)*(sp2) + (253680562226857/12500000000000 : ℝ)*(sp3) + (1003085183/10000000000000 : ℝ)*(sp4) + (2479870261/50000000000000 : ℝ)*(sp7) + (2029449457555377/100000000000000 : ℝ)*(f.failure) + (2224979911445693/50000000000000 : ℝ)*(f.sum) + (15015503897699/11957500000000000000000000000 : ℝ)*base66 + (14942735341606099481/1195750000000000000000000000000000 : ℝ)*base68 + (2354362685279599481/1195750000000000000000000000000000 : ℝ)*base70 + (29531256587900519/1195750000000000000000000000000000 : ℝ)*base71 + (187724574247263/23915000000000000000000000000 : ℝ)*base74 + (10741708737942900519/1195750000000000000000000000000000 : ℝ)*base75 + (3263805269531900519/1195750000000000000000000000000000 : ℝ)*base77 + (50520401035599481/1195750000000000000000000000000000 : ℝ)*base80 + (41351582589773/23915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38271967/5000000000000000000000 : ℝ)*base90 + (38271967/5000000000000000000000 : ℝ)*base92 + (38271967/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2187423951919890034301004363/597875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606491223/100000000000000 : ℝ)*(base19) + (655934631/100000000000000 : ℝ)*(base23) + (73858909/100000000000000 : ℝ)*(upper3) + (5934859/20000000000000 : ℝ)*(lower4) + (73505291/100000000000000 : ℝ)*(upper5) + (3273235760753269/100000000000000 : ℝ)*(major0) + (3273235760753269/100000000000000 : ℝ)*(major1) + (3273235760753269/100000000000000 : ℝ)*(major2) + (55437779/625000000000 : ℝ)*(sp1) + (9502560817/100000000000000 : ℝ)*(sp2) + (4496017067288651/100000000000000 : ℝ)*(sp4) + (1124001897688197/25000000000000 : ℝ)*(sp5) + (1124001727198301/25000000000000 : ℝ)*(sp6) + (1025227166131201/50000000000000 : ℝ)*(sp7) + (1025227166131201/50000000000000 : ℝ)*(f.failure) + (4496017067288651/100000000000000 : ℝ)*(f.sum) + (116397923694251/23915000000000000000000000000 : ℝ)*base66 + (12883369196621381879/2391500000000000000000000000000000 : ℝ)*base68 + (3281561654544381879/2391500000000000000000000000000000 : ℝ)*base70 + (5878292546093381879/2391500000000000000000000000000000 : ℝ)*base72 + (32775539735433/11957500000000000000000000000 : ℝ)*base74 + (29527124583770618121/2391500000000000000000000000000000 : ℝ)*base75 + (18050249988132381879/2391500000000000000000000000000000 : ℝ)*base78 + (36524949365129381879/2391500000000000000000000000000000 : ℝ)*base80 + (40142877020621/23915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2382129/2500000000000000000000 : ℝ)*base89 + (2382129/2500000000000000000000 : ℝ)*base91 + (2382129/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1465_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1465_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1465_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1465_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1465_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
