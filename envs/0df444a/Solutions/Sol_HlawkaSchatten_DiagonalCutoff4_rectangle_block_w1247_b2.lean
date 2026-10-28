-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:14.775281+00:00
-- url     : https://prove2.me/submissions/a9502e80-658e-4725-91b1-c2a5ea4e08bb

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
theorem support_rectangle_w1247_s6_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-211764783/1000000000 : ℝ)*x 0 + (5391291577/10000000000 : ℝ)*x 1 + (5267103159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211764783/1000000000 : ℝ)^1055 ≤ (2575650509719/20000000000000 : ℝ)^799 := by
    have hnat : (211764783 : ℕ)^1055*20000000000000^799 ≤ 2575650509719^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211764783 1000000000 2575650509719 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391291577/10000000000 : ℝ)^1055 ≤ (11057757828523/25000000000000 : ℝ)^799 := by
    have hnat : (5391291577 : ℕ)^1055*25000000000000^799 ≤ 11057757828523^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391291577 10000000000 11057757828523 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267103159/10000000000 : ℝ)^1055 ≤ (8578143224113/20000000000000 : ℝ)^799 := by
    have hnat : (5267103159 : ℕ)^1055*20000000000000^799 ≤ 8578143224113^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267103159 10000000000 8578143224113 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211764783/1000000000 : ℝ), (5391291577/10000000000 : ℝ), (5267103159/10000000000 : ℝ)] ![(2575650509719/20000000000000 : ℝ), (11057757828523/25000000000000 : ℝ), (8578143224113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211764783/1000000000 : ℝ)|^1055 ≤ (2575650509719/20000000000000 : ℝ)^799
        have hw : |(-211764783/1000000000 : ℝ)|=(211764783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391291577/10000000000 : ℝ)|^1055 ≤ (11057757828523/25000000000000 : ℝ)^799
        have hw : |(5391291577/10000000000 : ℝ)|=(5391291577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267103159/10000000000 : ℝ)|^1055 ≤ (8578143224113/20000000000000 : ℝ)^799
        have hw : |(5267103159/10000000000 : ℝ)|=(5267103159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344329477/10000000000 : ℝ)*x 0 + (-545153989/2500000000 : ℝ)*x 1 + (2633551577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344329477/10000000000 : ℝ)^1055 ≤ (43723012532959/100000000000000 : ℝ)^799 := by
    have hnat : (5344329477 : ℕ)^1055*100000000000000^799 ≤ 43723012532959^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344329477 10000000000 43723012532959 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545153989/2500000000 : ℝ)^1055 ≤ (1673283923669/12500000000000 : ℝ)^799 := by
    have hnat : (545153989 : ℕ)^1055*12500000000000^799 ≤ 1673283923669^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545153989 2500000000 1673283923669 12500000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633551577/5000000000 : ℝ)^1055 ≤ (10722679016701/25000000000000 : ℝ)^799 := by
    have hnat : (2633551577 : ℕ)^1055*25000000000000^799 ≤ 10722679016701^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633551577 5000000000 10722679016701 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344329477/10000000000 : ℝ), (-545153989/2500000000 : ℝ), (2633551577/5000000000 : ℝ)] ![(43723012532959/100000000000000 : ℝ), (1673283923669/12500000000000 : ℝ), (10722679016701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344329477/10000000000 : ℝ)|^1055 ≤ (43723012532959/100000000000000 : ℝ)^799
        have hw : |(5344329477/10000000000 : ℝ)|=(5344329477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545153989/2500000000 : ℝ)|^1055 ≤ (1673283923669/12500000000000 : ℝ)^799
        have hw : |(-545153989/2500000000 : ℝ)|=(545153989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633551577/5000000000 : ℝ)|^1055 ≤ (10722679016701/25000000000000 : ℝ)^799
        have hw : |(2633551577/5000000000 : ℝ)|=(2633551577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344329491/10000000000 : ℝ)*x 0 + (5267103149/10000000000 : ℝ)*x 1 + (-272576993/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344329491/10000000000 : ℝ)^1055 ≤ (21861506342097/50000000000000 : ℝ)^799 := by
    have hnat : (5344329491 : ℕ)^1055*50000000000000^799 ≤ 21861506342097^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344329491 10000000000 21861506342097 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267103149/10000000000 : ℝ)^1055 ≤ (42890716013043/100000000000000 : ℝ)^799 := by
    have hnat : (5267103149 : ℕ)^1055*100000000000000^799 ≤ 42890716013043^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267103149 10000000000 42890716013043 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272576993/1250000000 : ℝ)^1055 ≤ (2677254258417/20000000000000 : ℝ)^799 := by
    have hnat : (272576993 : ℕ)^1055*20000000000000^799 ≤ 2677254258417^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272576993 1250000000 2677254258417 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344329491/10000000000 : ℝ), (5267103149/10000000000 : ℝ), (-272576993/1250000000 : ℝ)] ![(21861506342097/50000000000000 : ℝ), (42890716013043/100000000000000 : ℝ), (2677254258417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344329491/10000000000 : ℝ)|^1055 ≤ (21861506342097/50000000000000 : ℝ)^799
        have hw : |(5344329491/10000000000 : ℝ)|=(5344329491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267103149/10000000000 : ℝ)|^1055 ≤ (42890716013043/100000000000000 : ℝ)^799
        have hw : |(5267103149/10000000000 : ℝ)|=(5267103149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272576993/1250000000 : ℝ)|^1055 ≤ (2677254258417/20000000000000 : ℝ)^799
        have hw : |(-272576993/1250000000 : ℝ)|=(272576993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350078633/10000000000 : ℝ)*x 0 + (845153799/2000000000 : ℝ)*x 1 + (1119484303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350078633/10000000000 : ℝ)^1055 ≤ (33317422768277/100000000000000 : ℝ)^799 := by
    have hnat : (4350078633 : ℕ)^1055*100000000000000^799 ≤ 33317422768277^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350078633 10000000000 33317422768277 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845153799/2000000000 : ℝ)^1055 ≤ (2004129521649/6250000000000 : ℝ)^799 := by
    have hnat : (845153799 : ℕ)^1055*6250000000000^799 ≤ 2004129521649^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845153799 2000000000 2004129521649 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119484303/2500000000 : ℝ)^1055 ≤ (17308252432543/50000000000000 : ℝ)^799 := by
    have hnat : (1119484303 : ℕ)^1055*50000000000000^799 ≤ 17308252432543^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119484303 2500000000 17308252432543 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350078633/10000000000 : ℝ), (845153799/2000000000 : ℝ), (1119484303/2500000000 : ℝ)] ![(33317422768277/100000000000000 : ℝ), (2004129521649/6250000000000 : ℝ), (17308252432543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350078633/10000000000 : ℝ)|^1055 ≤ (33317422768277/100000000000000 : ℝ)^799
        have hw : |(4350078633/10000000000 : ℝ)|=(4350078633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845153799/2000000000 : ℝ)|^1055 ≤ (2004129521649/6250000000000 : ℝ)^799
        have hw : |(845153799/2000000000 : ℝ)|=(845153799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119484303/2500000000 : ℝ)|^1055 ≤ (17308252432543/50000000000000 : ℝ)^799
        have hw : |(1119484303/2500000000 : ℝ)|=(1119484303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058826257/5000000000 : ℝ)*x 0 + (5267417313/10000000000 : ℝ)*x 1 + (2695488141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058826257/5000000000 : ℝ)^1055 ≤ (12878290160551/100000000000000 : ℝ)^799 := by
    have hnat : (1058826257 : ℕ)^1055*100000000000000^799 ≤ 12878290160551^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058826257 5000000000 12878290160551 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267417313/10000000000 : ℝ)^1055 ≤ (1715763759923/4000000000000 : ℝ)^799 := by
    have hnat : (5267417313 : ℕ)^1055*4000000000000^799 ≤ 1715763759923^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267417313 10000000000 1715763759923 4000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695488141/5000000000 : ℝ)^1055 ≤ (44227615824703/100000000000000 : ℝ)^799 := by
    have hnat : (2695488141 : ℕ)^1055*100000000000000^799 ≤ 44227615824703^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695488141 5000000000 44227615824703 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058826257/5000000000 : ℝ), (5267417313/10000000000 : ℝ), (2695488141/5000000000 : ℝ)] ![(12878290160551/100000000000000 : ℝ), (1715763759923/4000000000000 : ℝ), (44227615824703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058826257/5000000000 : ℝ)|^1055 ≤ (12878290160551/100000000000000 : ℝ)^799
        have hw : |(-1058826257/5000000000 : ℝ)|=(1058826257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267417313/10000000000 : ℝ)|^1055 ≤ (1715763759923/4000000000000 : ℝ)^799
        have hw : |(5267417313/10000000000 : ℝ)|=(5267417313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695488141/5000000000 : ℝ)|^1055 ≤ (44227615824703/100000000000000 : ℝ)^799
        have hw : |(2695488141/5000000000 : ℝ)|=(2695488141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328157893/2500000000 : ℝ)*x 0 + (-2056742819/10000000000 : ℝ)*x 1 + (5390976289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328157893/2500000000 : ℝ)^1055 ≤ (8676184615563/20000000000000 : ℝ)^799 := by
    have hnat : (1328157893 : ℕ)^1055*20000000000000^799 ≤ 8676184615563^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328157893 2500000000 8676184615563 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056742819/10000000000 : ℝ)^1055 ≤ (6195730502327/50000000000000 : ℝ)^799 := by
    have hnat : (2056742819 : ℕ)^1055*50000000000000^799 ≤ 6195730502327^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056742819 10000000000 6195730502327 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390976289/10000000000 : ℝ)^1055 ≤ (44227615900531/100000000000000 : ℝ)^799 := by
    have hnat : (5390976289 : ℕ)^1055*100000000000000^799 ≤ 44227615900531^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390976289 10000000000 44227615900531 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328157893/2500000000 : ℝ), (-2056742819/10000000000 : ℝ), (5390976289/10000000000 : ℝ)] ![(8676184615563/20000000000000 : ℝ), (6195730502327/50000000000000 : ℝ), (44227615900531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328157893/2500000000 : ℝ)|^1055 ≤ (8676184615563/20000000000000 : ℝ)^799
        have hw : |(1328157893/2500000000 : ℝ)|=(1328157893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056742819/10000000000 : ℝ)|^1055 ≤ (6195730502327/50000000000000 : ℝ)^799
        have hw : |(-2056742819/10000000000 : ℝ)|=(2056742819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390976289/10000000000 : ℝ)|^1055 ≤ (44227615900531/100000000000000 : ℝ)^799
        have hw : |(5390976289/10000000000 : ℝ)|=(5390976289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312631571/10000000000 : ℝ)*x 0 + (5390976289/10000000000 : ℝ)*x 1 + (-2056742821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312631571/10000000000 : ℝ)^1055 ≤ (43380923067033/100000000000000 : ℝ)^799 := by
    have hnat : (5312631571 : ℕ)^1055*100000000000000^799 ≤ 43380923067033^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312631571 10000000000 43380923067033 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390976289/10000000000 : ℝ)^1055 ≤ (44227615900531/100000000000000 : ℝ)^799 := by
    have hnat : (5390976289 : ℕ)^1055*100000000000000^799 ≤ 44227615900531^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390976289 10000000000 44227615900531 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056742821/10000000000 : ℝ)^1055 ≤ (3097865255141/25000000000000 : ℝ)^799 := by
    have hnat : (2056742821 : ℕ)^1055*25000000000000^799 ≤ 3097865255141^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056742821 10000000000 3097865255141 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312631571/10000000000 : ℝ), (5390976289/10000000000 : ℝ), (-2056742821/10000000000 : ℝ)] ![(43380923067033/100000000000000 : ℝ), (44227615900531/100000000000000 : ℝ), (3097865255141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312631571/10000000000 : ℝ)|^1055 ≤ (43380923067033/100000000000000 : ℝ)^799
        have hw : |(5312631571/10000000000 : ℝ)|=(5312631571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390976289/10000000000 : ℝ)|^1055 ≤ (44227615900531/100000000000000 : ℝ)^799
        have hw : |(5390976289/10000000000 : ℝ)|=(5390976289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056742821/10000000000 : ℝ)|^1055 ≤ (3097865255141/25000000000000 : ℝ)^799
        have hw : |(-2056742821/10000000000 : ℝ)|=(2056742821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s6_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1087522033/2500000000 : ℝ)*x 0 + (4477299323/10000000000 : ℝ)*x 1 + (528301153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087522033/2500000000 : ℝ)^1055 ≤ (3331751883169/10000000000000 : ℝ)^799 := by
    have hnat : (1087522033 : ℕ)^1055*10000000000000^799 ≤ 3331751883169^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087522033 2500000000 3331751883169 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477299323/10000000000 : ℝ)^1055 ≤ (17304996944513/50000000000000 : ℝ)^799 := by
    have hnat : (4477299323 : ℕ)^1055*50000000000000^799 ≤ 17304996944513^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477299323 10000000000 17304996944513 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528301153/1250000000 : ℝ)^1055 ≤ (32072487271317/100000000000000 : ℝ)^799 := by
    have hnat : (528301153 : ℕ)^1055*100000000000000^799 ≤ 32072487271317^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528301153 1250000000 32072487271317 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087522033/2500000000 : ℝ), (4477299323/10000000000 : ℝ), (528301153/1250000000 : ℝ)] ![(3331751883169/10000000000000 : ℝ), (17304996944513/50000000000000 : ℝ), (32072487271317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087522033/2500000000 : ℝ)|^1055 ≤ (3331751883169/10000000000000 : ℝ)^799
        have hw : |(1087522033/2500000000 : ℝ)|=(1087522033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477299323/10000000000 : ℝ)|^1055 ≤ (17304996944513/50000000000000 : ℝ)^799
        have hw : |(4477299323/10000000000 : ℝ)|=(4477299323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528301153/1250000000 : ℝ)|^1055 ≤ (32072487271317/100000000000000 : ℝ)^799
        have hw : |(528301153/1250000000 : ℝ)|=(528301153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (287/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14111/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (573/5000 : ℝ) ^ (8439/2048 : ℝ) ≤ (13282229815157417/100000000000000000000 : ℝ) := by
    have hpowers : (573/5000 : ℝ)^8439 ≤ (13282229815157417/100000000000000000000 : ℝ)^2048 := by
      have hnat : (573 : ℕ)^8439*100000000000000000000^2048 ≤ 13282229815157417^2048*5000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 5000 13282229815157417 100000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/5000 : ℝ)) (X := (13282229815157417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3533/25000 : ℝ) ^ (8439/2048 : ℝ) ≤ (7875251535157559/25000000000000000000 : ℝ) := by
    have hpowers : (3533/25000 : ℝ)^8439 ≤ (7875251535157559/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3533 : ℕ)^8439*25000000000000000000^2048 ≤ 7875251535157559^2048*25000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3533 25000 7875251535157559 25000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3533/25000 : ℝ)) (X := (7875251535157559/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013282229815157417/50000000000000000000 : ℝ) ≤ (1250080576107581/1250000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50013282229815157417/50000000000000000000 : ℝ)^2048 ≤ (1250080576107581/1250000000000000 : ℝ)^8439 := by
      have hnat : (50013282229815157417 : ℕ)^2048*1250000000000000^8439 ≤ 1250080576107581^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013282229815157417 50000000000000000000 1250080576107581 1250000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250080576107581/1250000000000000 : ℝ)) (X := (50013282229815157417/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044783235955787653/100000000000000000000 : ℝ) ≤ (5000543313890929/5000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (100044783235955787653/100000000000000000000 : ℝ)^2048 ≤ (5000543313890929/5000000000000000 : ℝ)^8439 := by
      have hnat : (100044783235955787653 : ℕ)^2048*5000000000000000^8439 ≤ 5000543313890929^8439*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044783235955787653 100000000000000000000 5000543313890929 5000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000543313890929/5000000000000000 : ℝ)) (X := (100044783235955787653/100000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507875251535157559/12500000000000000000 : ℝ) ≤ (2500382161675767/2500000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (12507875251535157559/12500000000000000000 : ℝ)^2048 ≤ (2500382161675767/2500000000000000 : ℝ)^8439 := by
      have hnat : (12507875251535157559 : ℕ)^2048*2500000000000000^8439 ≤ 2500382161675767^8439*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507875251535157559 12500000000000000000 2500382161675767 2500000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500382161675767/2500000000000000 : ℝ)) (X := (12507875251535157559/12500000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13282229815157417/100000000000000000000 : ℝ) ≤ ((1669474457575094891/1670000000000000000 : ℝ)+2*(44201892121/26720000000000 : ℝ)*(573/5000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (1669474457575094891/1670000000000000000 : ℝ)+2*(44201892121/26720000000000 : ℝ)*(573/5000 : ℝ)=(1250080576107581/1250000000000000 : ℝ) by norm_num, show 1+2*(13282229815157417/100000000000000000000 : ℝ)=(50013282229815157417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7875251535157559/25000000000000000000 : ℝ)+(13282229815157417/100000000000000000000 : ℝ) ≤ ((1669474457575094891/1670000000000000000 : ℝ)+(44201892121/26720000000000 : ℝ)*((3533/25000 : ℝ)+(573/5000 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (1669474457575094891/1670000000000000000 : ℝ)+(44201892121/26720000000000 : ℝ)*((3533/25000 : ℝ)+(573/5000 : ℝ))=(5000543313890929/5000000000000000 : ℝ) by norm_num, show 1+(7875251535157559/25000000000000000000 : ℝ)+(13282229815157417/100000000000000000000 : ℝ)=(100044783235955787653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7875251535157559/25000000000000000000 : ℝ) ≤ ((1669474457575094891/1670000000000000000 : ℝ)+2*(44201892121/26720000000000 : ℝ)*(3533/25000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (1669474457575094891/1670000000000000000 : ℝ)+2*(44201892121/26720000000000 : ℝ)*(3533/25000 : ℝ)=(2500382161675767/2500000000000000 : ℝ) by norm_num, show 1+2*(7875251535157559/25000000000000000000 : ℝ)=(12507875251535157559/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1669474457575094891/1670000000000000000 : ℝ)*(X 1 0+X 2 0)+(44201892121/26720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (3533/25000 : ℝ)) (c := (1669474457575094891/1670000000000000000 : ℝ)) (alpha := (44201892121/26720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1669474457575094891/1670000000000000000 : ℝ)*(X 0 1+X 2 1)+(44201892121/26720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (3533/25000 : ℝ)) (c := (1669474457575094891/1670000000000000000 : ℝ)) (alpha := (44201892121/26720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1669474457575094891/1670000000000000000 : ℝ)*(X 0 2+X 1 2)+(44201892121/26720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (3533/25000 : ℝ)) (c := (1669474457575094891/1670000000000000000 : ℝ)) (alpha := (44201892121/26720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211764783/1000000000 : ℝ)*X 0 0+(5391291577/10000000000 : ℝ)*X 0 1+(5267103159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344329477/10000000000 : ℝ)*X 1 0+(-545153989/2500000000 : ℝ)*X 1 1+(2633551577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344329491/10000000000 : ℝ)*X 2 0+(5267103149/10000000000 : ℝ)*X 2 1+(-272576993/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350078633/10000000000 : ℝ)*X 0 0+(845153799/2000000000 : ℝ)*X 0 1+(1119484303/2500000000 : ℝ)*X 0 2+(4350078633/10000000000 : ℝ)*X 1 0+(845153799/2000000000 : ℝ)*X 1 1+(1119484303/2500000000 : ℝ)*X 1 2+(4350078633/10000000000 : ℝ)*X 2 0+(845153799/2000000000 : ℝ)*X 2 1+(1119484303/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058826257/5000000000 : ℝ)*X 0 0+(5267417313/10000000000 : ℝ)*X 0 1+(2695488141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328157893/2500000000 : ℝ)*X 1 0+(-2056742819/10000000000 : ℝ)*X 1 1+(5390976289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312631571/10000000000 : ℝ)*X 2 0+(5390976289/10000000000 : ℝ)*X 2 1+(-2056742821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087522033/2500000000 : ℝ)*X 0 0+(4477299323/10000000000 : ℝ)*X 0 1+(528301153/1250000000 : ℝ)*X 0 2+(1087522033/2500000000 : ℝ)*X 1 0+(4477299323/10000000000 : ℝ)*X 1 1+(528301153/1250000000 : ℝ)*X 1 2+(1087522033/2500000000 : ℝ)*X 2 0+(4477299323/10000000000 : ℝ)*X 2 1+(528301153/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (217745853372174871548465891/20875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1017999513/50000000000000 : ℝ)*(base19) + (953879571/50000000000000 : ℝ)*(base23) + (79808971/100000000000000 : ℝ)*(lower2) + (5158433/2000000000000 : ℝ)*(upper3) + (85943621/50000000000000 : ℝ)*(upper5) + (3004514850250083/50000000000000 : ℝ)*(major0) + (3004514850250083/50000000000000 : ℝ)*(major1) + (3004514850250083/50000000000000 : ℝ)*(major2) + (8052338761863079/100000000000000 : ℝ)*(sp0) + (8052393370071813/100000000000000 : ℝ)*(sp1) + (8052393498311697/100000000000000 : ℝ)*(sp2) + (991408453192013/25000000000000 : ℝ)*(sp3) + (708052597/1250000000000 : ℝ)*(sp4) + (3729307933/12500000000000 : ℝ)*(sp7) + (991415911807879/25000000000000 : ℝ)*(f.failure) + (8052395406070839/100000000000000 : ℝ)*(f.sum) + (1178233293229/668000000000000000000000000 : ℝ)*base66 + (396227039045813453/83500000000000000000000000000000 : ℝ)*base67 + (1287629014915186547/83500000000000000000000000000000 : ℝ)*base70 + (544484888730813453/83500000000000000000000000000000 : ℝ)*base71 + (164801127531/668000000000000000000000000 : ℝ)*base73 + (675282027781313453/83500000000000000000000000000000 : ℝ)*base75 + (1282238749159813453/83500000000000000000000000000000 : ℝ)*base77 + (177515539980813453/83500000000000000000000000000000 : ℝ)*base79 + (2604935026613/668000000000000000000000000 : ℝ)*base82 + (43170461/2500000000000000000000 : ℝ)*base89 + (43170461/2500000000000000000000 : ℝ)*base91 + (43170461/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (828520425877834885071/267200000000000000000000000 : ℝ) := by norm_num
    linear_combination (537890767/100000000000000 : ℝ)*(base19) + (587421243/100000000000000 : ℝ)*(base23) + (2491493/4000000000000 : ℝ)*(upper3) + (23313617/100000000000000 : ℝ)*(lower4) + (15266629/25000000000000 : ℝ)*(upper5) + (6039554844125023/100000000000000 : ℝ)*(major0) + (6039554844125023/100000000000000 : ℝ)*(major1) + (6039554844125023/100000000000000 : ℝ)*(major2) + (3860665961/25000000000000 : ℝ)*(sp1) + (4161112021/25000000000000 : ℝ)*(sp2) + (404665042314193/5000000000000 : ℝ)*(sp4) + (252915152054039/3125000000000 : ℝ)*(sp5) + (8093283614414533/100000000000000 : ℝ)*(sp6) + (3985808738607839/100000000000000 : ℝ)*(sp7) + (3985808738607839/100000000000000 : ℝ)*(f.failure) + (404665042314193/5000000000000 : ℝ)*(f.sum) + (985434562821/267200000000000000000000000 : ℝ)*base66 + (1014626861769994993/167000000000000000000000000000000 : ℝ)*base67 + (1947093802823005007/167000000000000000000000000000000 : ℝ)*base70 + (2250616091735005007/167000000000000000000000000000000 : ℝ)*base72 + (4191314007727/1336000000000000000000000000 : ℝ)*base73 + (3654661323800994993/167000000000000000000000000000000 : ℝ)*base75 + (1719008188616005007/167000000000000000000000000000000 : ℝ)*base78 + (1557885147478994993/167000000000000000000000000000000 : ℝ)*base79 + (2016827012991/1336000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (133312101/10000000000000000000000 : ℝ)*base89 + (133312101/10000000000000000000000 : ℝ)*base91 + (133312101/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1247_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s7_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-423532883/2000000000 : ℝ)*x 0 + (5391099481/10000000000 : ℝ)*x 1 + (5267284307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423532883/2000000000 : ℝ)^1055 ≤ (3219596431067/25000000000000 : ℝ)^799 := by
    have hnat : (423532883 : ℕ)^1055*25000000000000^799 ≤ 3219596431067^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423532883 2000000000 3219596431067 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391099481/10000000000 : ℝ)^1055 ≤ (11057237598063/25000000000000 : ℝ)^799 := by
    have hnat : (5391099481 : ℕ)^1055*25000000000000^799 ≤ 11057237598063^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391099481 10000000000 11057237598063 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267284307/10000000000 : ℝ)^1055 ≤ (10723165967503/25000000000000 : ℝ)^799 := by
    have hnat : (5267284307 : ℕ)^1055*25000000000000^799 ≤ 10723165967503^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267284307 10000000000 10723165967503 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423532883/2000000000 : ℝ), (5391099481/10000000000 : ℝ), (5267284307/10000000000 : ℝ)] ![(3219596431067/25000000000000 : ℝ), (11057237598063/25000000000000 : ℝ), (10723165967503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423532883/2000000000 : ℝ)|^1055 ≤ (3219596431067/25000000000000 : ℝ)^799
        have hw : |(-423532883/2000000000 : ℝ)|=(423532883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391099481/10000000000 : ℝ)|^1055 ≤ (11057237598063/25000000000000 : ℝ)^799
        have hw : |(5391099481/10000000000 : ℝ)|=(5391099481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267284307/10000000000 : ℝ)|^1055 ≤ (10723165967503/25000000000000 : ℝ)^799
        have hw : |(5267284307/10000000000 : ℝ)|=(5267284307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334017543/625000000 : ℝ)*x 0 + (-2180440657/10000000000 : ℝ)*x 1 + (5267284319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334017543/625000000 : ℝ)^1055 ≤ (683163835823/1562500000000 : ℝ)^799 := by
    have hnat : (334017543 : ℕ)^1055*1562500000000^799 ≤ 683163835823^799*625000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334017543 625000000 683163835823 1562500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180440657/10000000000 : ℝ)^1055 ≤ (6692425250481/50000000000000 : ℝ)^799 := by
    have hnat : (2180440657 : ℕ)^1055*50000000000000^799 ≤ 6692425250481^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180440657 10000000000 6692425250481 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267284319/10000000000 : ℝ)^1055 ≤ (134039574997/312500000000 : ℝ)^799 := by
    have hnat : (5267284319 : ℕ)^1055*312500000000^799 ≤ 134039574997^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267284319 10000000000 134039574997 312500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334017543/625000000 : ℝ), (-2180440657/10000000000 : ℝ), (5267284319/10000000000 : ℝ)] ![(683163835823/1562500000000 : ℝ), (6692425250481/50000000000000 : ℝ), (134039574997/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334017543/625000000 : ℝ)|^1055 ≤ (683163835823/1562500000000 : ℝ)^799
        have hw : |(334017543/625000000 : ℝ)|=(334017543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180440657/10000000000 : ℝ)|^1055 ≤ (6692425250481/50000000000000 : ℝ)^799
        have hw : |(-2180440657/10000000000 : ℝ)|=(2180440657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267284319/10000000000 : ℝ)|^1055 ≤ (134039574997/312500000000 : ℝ)^799
        have hw : |(5267284319/10000000000 : ℝ)|=(5267284319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672140341/5000000000 : ℝ)*x 0 + (526728431/1000000000 : ℝ)*x 1 + (-87217627/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672140341/5000000000 : ℝ)^1055 ≤ (43722485427857/100000000000000 : ℝ)^799 := by
    have hnat : (2672140341 : ℕ)^1055*100000000000000^799 ≤ 43722485427857^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672140341 5000000000 43722485427857 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526728431/1000000000 : ℝ)^1055 ≤ (42892663902269/100000000000000 : ℝ)^799 := by
    have hnat : (526728431 : ℕ)^1055*100000000000000^799 ≤ 42892663902269^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526728431 1000000000 42892663902269 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87217627/400000000 : ℝ)^1055 ≤ (13384850646859/100000000000000 : ℝ)^799 := by
    have hnat : (87217627 : ℕ)^1055*100000000000000^799 ≤ 13384850646859^799*400000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87217627 400000000 13384850646859 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672140341/5000000000 : ℝ), (526728431/1000000000 : ℝ), (-87217627/400000000 : ℝ)] ![(43722485427857/100000000000000 : ℝ), (42892663902269/100000000000000 : ℝ), (13384850646859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672140341/5000000000 : ℝ)|^1055 ≤ (43722485427857/100000000000000 : ℝ)^799
        have hw : |(2672140341/5000000000 : ℝ)|=(2672140341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526728431/1000000000 : ℝ)|^1055 ≤ (42892663902269/100000000000000 : ℝ)^799
        have hw : |(526728431/1000000000 : ℝ)|=(526728431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87217627/400000000 : ℝ)|^1055 ≤ (13384850646859/100000000000000 : ℝ)^799
        have hw : |(-87217627/400000000 : ℝ)|=(87217627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350088059/10000000000 : ℝ)*x 0 + (845229347/2000000000 : ℝ)*x 1 + (4477557073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350088059/10000000000 : ℝ)^1055 ≤ (52058622021/156250000000 : ℝ)^799 := by
    have hnat : (4350088059 : ℕ)^1055*156250000000^799 ≤ 52058622021^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350088059 10000000000 52058622021 156250000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845229347/2000000000 : ℝ)^1055 ≤ (32069857163431/100000000000000 : ℝ)^799 := by
    have hnat : (845229347 : ℕ)^1055*100000000000000^799 ≤ 32069857163431^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845229347 2000000000 32069857163431 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477557073/10000000000 : ℝ)^1055 ≤ (6922524944977/20000000000000 : ℝ)^799 := by
    have hnat : (4477557073 : ℕ)^1055*20000000000000^799 ≤ 6922524944977^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477557073 10000000000 6922524944977 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350088059/10000000000 : ℝ), (845229347/2000000000 : ℝ), (4477557073/10000000000 : ℝ)] ![(52058622021/156250000000 : ℝ), (32069857163431/100000000000000 : ℝ), (6922524944977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350088059/10000000000 : ℝ)|^1055 ≤ (52058622021/156250000000 : ℝ)^799
        have hw : |(4350088059/10000000000 : ℝ)|=(4350088059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845229347/2000000000 : ℝ)|^1055 ≤ (32069857163431/100000000000000 : ℝ)^799
        have hw : |(845229347/2000000000 : ℝ)|=(845229347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477557073/10000000000 : ℝ)|^1055 ≤ (6922524944977/20000000000000 : ℝ)^799
        have hw : |(4477557073/10000000000 : ℝ)|=(4477557073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-33088579/156250000 : ℝ)*x 0 + (1316899159/2500000000 : ℝ)*x 1 + (2695393011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33088579/156250000 : ℝ)^1055 ≤ (12878422991033/100000000000000 : ℝ)^799 := by
    have hnat : (33088579 : ℕ)^1055*100000000000000^799 ≤ 12878422991033^799*156250000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33088579 156250000 12878422991033 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316899159/2500000000 : ℝ)^1055 ≤ (8579204432279/20000000000000 : ℝ)^799 := by
    have hnat : (1316899159 : ℕ)^1055*20000000000000^799 ≤ 8579204432279^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316899159 2500000000 8579204432279 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695393011/5000000000 : ℝ)^1055 ≤ (22112777415121/50000000000000 : ℝ)^799 := by
    have hnat : (2695393011 : ℕ)^1055*50000000000000^799 ≤ 22112777415121^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695393011 5000000000 22112777415121 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33088579/156250000 : ℝ), (1316899159/2500000000 : ℝ), (2695393011/5000000000 : ℝ)] ![(12878422991033/100000000000000 : ℝ), (8579204432279/20000000000000 : ℝ), (22112777415121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33088579/156250000 : ℝ)|^1055 ≤ (12878422991033/100000000000000 : ℝ)^799
        have hw : |(-33088579/156250000 : ℝ)|=(33088579/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316899159/2500000000 : ℝ)|^1055 ≤ (8579204432279/20000000000000 : ℝ)^799
        have hw : |(1316899159/2500000000 : ℝ)|=(1316899159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695393011/5000000000 : ℝ)|^1055 ≤ (22112777415121/50000000000000 : ℝ)^799
        have hw : |(2695393011/5000000000 : ℝ)|=(2695393011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664084753/1250000000 : ℝ)*x 0 + (-2056938947/10000000000 : ℝ)*x 1 + (269539301/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664084753/1250000000 : ℝ)^1055 ≤ (1735256956749/4000000000000 : ℝ)^799 := by
    have hnat : (664084753 : ℕ)^1055*4000000000000^799 ≤ 1735256956749^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664084753 1250000000 1735256956749 4000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056938947/10000000000 : ℝ)^1055 ≤ (2478604251109/20000000000000 : ℝ)^799 := by
    have hnat : (2056938947 : ℕ)^1055*20000000000000^799 ≤ 2478604251109^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056938947 10000000000 2478604251109 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269539301/500000000 : ℝ)^1055 ≤ (44225554808577/100000000000000 : ℝ)^799 := by
    have hnat : (269539301 : ℕ)^1055*100000000000000^799 ≤ 44225554808577^799*500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269539301 500000000 44225554808577 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664084753/1250000000 : ℝ), (-2056938947/10000000000 : ℝ), (269539301/500000000 : ℝ)] ![(1735256956749/4000000000000 : ℝ), (2478604251109/20000000000000 : ℝ), (44225554808577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664084753/1250000000 : ℝ)|^1055 ≤ (1735256956749/4000000000000 : ℝ)^799
        have hw : |(664084753/1250000000 : ℝ)|=(664084753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056938947/10000000000 : ℝ)|^1055 ≤ (2478604251109/20000000000000 : ℝ)^799
        have hw : |(-2056938947/10000000000 : ℝ)|=(2056938947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269539301/500000000 : ℝ)|^1055 ≤ (44225554808577/100000000000000 : ℝ)^799
        have hw : |(269539301/500000000 : ℝ)|=(269539301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062535607/2000000000 : ℝ)*x 0 + (269539301/500000000 : ℝ)*x 1 + (-2056938933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062535607/2000000000 : ℝ)^1055 ≤ (21690712018663/50000000000000 : ℝ)^799 := by
    have hnat : (1062535607 : ℕ)^1055*50000000000000^799 ≤ 21690712018663^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062535607 2000000000 21690712018663 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269539301/500000000 : ℝ)^1055 ≤ (44225554808577/100000000000000 : ℝ)^799 := by
    have hnat : (269539301 : ℕ)^1055*100000000000000^799 ≤ 44225554808577^799*500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269539301 500000000 44225554808577 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056938933/10000000000 : ℝ)^1055 ≤ (12393021144169/100000000000000 : ℝ)^799 := by
    have hnat : (2056938933 : ℕ)^1055*100000000000000^799 ≤ 12393021144169^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056938933 10000000000 12393021144169 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062535607/2000000000 : ℝ), (269539301/500000000 : ℝ), (-2056938933/10000000000 : ℝ)] ![(21690712018663/50000000000000 : ℝ), (44225554808577/100000000000000 : ℝ), (12393021144169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062535607/2000000000 : ℝ)|^1055 ≤ (21690712018663/50000000000000 : ℝ)^799
        have hw : |(1062535607/2000000000 : ℝ)|=(1062535607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269539301/500000000 : ℝ)|^1055 ≤ (44225554808577/100000000000000 : ℝ)^799
        have hw : |(269539301/500000000 : ℝ)|=(269539301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056938933/10000000000 : ℝ)|^1055 ≤ (12393021144169/100000000000000 : ℝ)^799
        have hw : |(-2056938933/10000000000 : ℝ)|=(2056938933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s7_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350097469/10000000000 : ℝ)*x 0 + (2238461457/5000000000 : ℝ)*x 1 + (2113391609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350097469/10000000000 : ℝ)^1055 ≤ (16658806628431/50000000000000 : ℝ)^799 := by
    have hnat : (4350097469 : ℕ)^1055*50000000000000^799 ≤ 16658806628431^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350097469 10000000000 16658806628431 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238461457/5000000000 : ℝ)^1055 ≤ (34606151996399/100000000000000 : ℝ)^799 := by
    have hnat : (2238461457 : ℕ)^1055*100000000000000^799 ≤ 34606151996399^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238461457 5000000000 34606151996399 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113391609/5000000000 : ℝ)^1055 ≤ (32076234736163/100000000000000 : ℝ)^799 := by
    have hnat : (2113391609 : ℕ)^1055*100000000000000^799 ≤ 32076234736163^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113391609 5000000000 32076234736163 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350097469/10000000000 : ℝ), (2238461457/5000000000 : ℝ), (2113391609/5000000000 : ℝ)] ![(16658806628431/50000000000000 : ℝ), (34606151996399/100000000000000 : ℝ), (32076234736163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350097469/10000000000 : ℝ)|^1055 ≤ (16658806628431/50000000000000 : ℝ)^799
        have hw : |(4350097469/10000000000 : ℝ)|=(4350097469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238461457/5000000000 : ℝ)|^1055 ≤ (34606151996399/100000000000000 : ℝ)^799
        have hw : |(2238461457/5000000000 : ℝ)|=(2238461457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113391609/5000000000 : ℝ)|^1055 ≤ (32076234736163/100000000000000 : ℝ)^799
        have hw : |(2113391609/5000000000 : ℝ)|=(2113391609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2871/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (287/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (287/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (287/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (287/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (287/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (287/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (287/2500 : ℝ) ^ (8439/2048 : ℝ) ≤ (13378006511614859/100000000000000000000 : ℝ) := by
    have hpowers : (287/2500 : ℝ)^8439 ≤ (13378006511614859/100000000000000000000 : ℝ)^2048 := by
      have hnat : (287 : ℕ)^8439*100000000000000000000^2048 ≤ 13378006511614859^2048*2500^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 2500 13378006511614859 100000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/2500 : ℝ)) (X := (13378006511614859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (31308566709559747/100000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^8439 ≤ (31308566709559747/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14111 : ℕ)^8439*100000000000000000000^2048 ≤ 31308566709559747^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 31308566709559747 100000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (31308566709559747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013378006511614859/50000000000000000000 : ℝ) ≤ (400025970263733/400000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50013378006511614859/50000000000000000000 : ℝ)^2048 ≤ (400025970263733/400000000000000 : ℝ)^8439 := by
      have hnat : (50013378006511614859 : ℕ)^2048*400000000000000^8439 ≤ 400025970263733^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013378006511614859 50000000000000000000 400025970263733 400000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025970263733/400000000000000 : ℝ)) (X := (50013378006511614859/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022343286610587303/50000000000000000000 : ℝ) ≤ (10001084282738143/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50022343286610587303/50000000000000000000 : ℝ)^2048 ≤ (10001084282738143/10000000000000000 : ℝ)^8439 := by
      have hnat : (50022343286610587303 : ℕ)^2048*10000000000000000^8439 ≤ 10001084282738143^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022343286610587303 50000000000000000000 10001084282738143 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084282738143/10000000000000000 : ℝ)) (X := (50022343286610587303/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031308566709559747/50000000000000000000 : ℝ) ≤ (10001519308882961/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50031308566709559747/50000000000000000000 : ℝ)^2048 ≤ (10001519308882961/10000000000000000 : ℝ)^8439 := by
      have hnat : (50031308566709559747 : ℕ)^2048*10000000000000000^8439 ≤ 10001519308882961^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031308566709559747 50000000000000000000 10001519308882961 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001519308882961/10000000000000000 : ℝ)) (X := (50031308566709559747/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13378006511614859/100000000000000000000 : ℝ) ≤ ((5260343998762403359/5262000000000000000 : ℝ)+2*(217513072409/131550000000000 : ℝ)*(287/2500 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (5260343998762403359/5262000000000000000 : ℝ)+2*(217513072409/131550000000000 : ℝ)*(287/2500 : ℝ)=(400025970263733/400000000000000 : ℝ) by norm_num, show 1+2*(13378006511614859/100000000000000000000 : ℝ)=(50013378006511614859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31308566709559747/100000000000000000000 : ℝ)+(13378006511614859/100000000000000000000 : ℝ) ≤ ((5260343998762403359/5262000000000000000 : ℝ)+(217513072409/131550000000000 : ℝ)*((14111/100000 : ℝ)+(287/2500 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (5260343998762403359/5262000000000000000 : ℝ)+(217513072409/131550000000000 : ℝ)*((14111/100000 : ℝ)+(287/2500 : ℝ))=(10001084282738143/10000000000000000 : ℝ) by norm_num, show 1+(31308566709559747/100000000000000000000 : ℝ)+(13378006511614859/100000000000000000000 : ℝ)=(50022343286610587303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31308566709559747/100000000000000000000 : ℝ) ≤ ((5260343998762403359/5262000000000000000 : ℝ)+2*(217513072409/131550000000000 : ℝ)*(14111/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (5260343998762403359/5262000000000000000 : ℝ)+2*(217513072409/131550000000000 : ℝ)*(14111/100000 : ℝ)=(10001519308882961/10000000000000000 : ℝ) by norm_num, show 1+2*(31308566709559747/100000000000000000000 : ℝ)=(50031308566709559747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5260343998762403359/5262000000000000000 : ℝ)*(X 1 0+X 2 0)+(217513072409/131550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (5260343998762403359/5262000000000000000 : ℝ)) (alpha := (217513072409/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5260343998762403359/5262000000000000000 : ℝ)*(X 0 1+X 2 1)+(217513072409/131550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (5260343998762403359/5262000000000000000 : ℝ)) (alpha := (217513072409/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5260343998762403359/5262000000000000000 : ℝ)*(X 0 2+X 1 2)+(217513072409/131550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (287/2500 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (5260343998762403359/5262000000000000000 : ℝ)) (alpha := (217513072409/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423532883/2000000000 : ℝ)*X 0 0+(5391099481/10000000000 : ℝ)*X 0 1+(5267284307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334017543/625000000 : ℝ)*X 1 0+(-2180440657/10000000000 : ℝ)*X 1 1+(5267284319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672140341/5000000000 : ℝ)*X 2 0+(526728431/1000000000 : ℝ)*X 2 1+(-87217627/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350088059/10000000000 : ℝ)*X 0 0+(845229347/2000000000 : ℝ)*X 0 1+(4477557073/10000000000 : ℝ)*X 0 2+(4350088059/10000000000 : ℝ)*X 1 0+(845229347/2000000000 : ℝ)*X 1 1+(4477557073/10000000000 : ℝ)*X 1 2+(4350088059/10000000000 : ℝ)*X 2 0+(845229347/2000000000 : ℝ)*X 2 1+(4477557073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33088579/156250000 : ℝ)*X 0 0+(1316899159/2500000000 : ℝ)*X 0 1+(2695393011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664084753/1250000000 : ℝ)*X 1 0+(-2056938947/10000000000 : ℝ)*X 1 1+(269539301/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062535607/2000000000 : ℝ)*X 2 0+(269539301/500000000 : ℝ)*X 2 1+(-2056938933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350097469/10000000000 : ℝ)*X 0 0+(2238461457/5000000000 : ℝ)*X 0 1+(2113391609/5000000000 : ℝ)*X 0 2+(4350097469/10000000000 : ℝ)*X 1 0+(2238461457/5000000000 : ℝ)*X 1 1+(2113391609/5000000000 : ℝ)*X 1 2+(4350097469/10000000000 : ℝ)*X 2 0+(2238461457/5000000000 : ℝ)*X 2 1+(2113391609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201632257107505283460638343/21925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220351477/12500000000000 : ℝ)*(base19) + (820303231/50000000000000 : ℝ)*(base23) + (60463979/100000000000000 : ℝ)*(lower2) + (124149113/50000000000000 : ℝ)*(upper3) + (663139/500000000000 : ℝ)*(upper5) + (1506783257363377/25000000000000 : ℝ)*(major0) + (1506783257363377/25000000000000 : ℝ)*(major1) + (1506783257363377/25000000000000 : ℝ)*(major2) + (1615321313381857/20000000000000 : ℝ)*(sp0) + (4038326518413119/50000000000000 : ℝ)*(sp1) + (1009581644878949/12500000000000 : ℝ)*(sp2) + (1988792258417811/50000000000000 : ℝ)*(sp3) + (48232728769/100000000000000 : ℝ)*(sp4) + (1321794243/5000000000000 : ℝ)*(sp7) + (3977610952720481/100000000000000 : ℝ)*(f.failure) + (4038327399819027/50000000000000 : ℝ)*(f.sum) + (74773322678801/13155000000000000000000000000 : ℝ)*base66 + (428796818013782219/43850000000000000000000000000000 : ℝ)*base68 + (243168785444217781/43850000000000000000000000000000 : ℝ)*base69 + (187274105185332219/43850000000000000000000000000000 : ℝ)*base72 + (39766082279069/3288750000000000000000000000 : ℝ)*base74 + (255025627724567781/43850000000000000000000000000000 : ℝ)*base75 + (380135789085332219/43850000000000000000000000000000 : ℝ)*base78 + (977514641555132219/43850000000000000000000000000000 : ℝ)*base80 + (5987896817893/6577500000000000000000000000 : ℝ)*base82 + (102706779/10000000000000000000000 : ℝ)*base89 + (102706779/10000000000000000000000 : ℝ)*base91 + (102706779/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58028356594696324925464679/17540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19214833/3125000000000 : ℝ)*(base19) + (168078137/25000000000000 : ℝ)*(base23) + (37099601/50000000000000 : ℝ)*(upper3) + (13404179/100000000000000 : ℝ)*(lower4) + (55767897/100000000000000 : ℝ)*(upper5) + (1211534802568519/20000000000000 : ℝ)*(major0) + (1211534802568519/20000000000000 : ℝ)*(major1) + (1211534802568519/20000000000000 : ℝ)*(major2) + (16808365043/100000000000000 : ℝ)*(sp1) + (9698601411/50000000000000 : ℝ)*(sp2) + (1623516283569197/20000000000000 : ℝ)*(sp4) + (2029390998651571/25000000000000 : ℝ)*(sp5) + (1623512269666123/20000000000000 : ℝ)*(sp6) + (199888324878053/5000000000000 : ℝ)*(sp7) + (199888324878053/5000000000000 : ℝ)*(f.failure) + (1623516283569197/20000000000000 : ℝ)*(f.sum) + (7438515744919/1315500000000000000000000000 : ℝ)*base66 + (100844334477365107/35080000000000000000000000000000 : ℝ)*base67 + (250740666468634893/35080000000000000000000000000000 : ℝ)*base70 + (246804698938165107/35080000000000000000000000000000 : ℝ)*base71 + (16224670893929/2631000000000000000000000000 : ℝ)*base74 + (2591367011794893/35080000000000000000000000000000 : ℝ)*base76 + (142240559724845107/35080000000000000000000000000000 : ℝ)*base77 + (68001783884565107/35080000000000000000000000000000 : ℝ)*base79 + (5369156908057/2631000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (2904327/500000000000000000000 : ℝ)*base89 + (2904327/500000000000000000000 : ℝ)*base91 + (2904327/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1247_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s8_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-33088547/156250000 : ℝ)*x 0 + (2695531259/5000000000 : ℝ)*x 1 + (5267319609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33088547/156250000 : ℝ)^1055 ≤ (2575681309159/20000000000000 : ℝ)^799 := by
    have hnat : (33088547 : ℕ)^1055*20000000000000^799 ≤ 2575681309159^799*156250000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33088547 156250000 2575681309159 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695531259/5000000000 : ℝ)^1055 ≤ (22114274992607/50000000000000 : ℝ)^799 := by
    have hnat : (2695531259 : ℕ)^1055*50000000000000^799 ≤ 22114274992607^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695531259 5000000000 22114274992607 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267319609/10000000000 : ℝ)^1055 ≤ (42893043448609/100000000000000 : ℝ)^799 := by
    have hnat : (5267319609 : ℕ)^1055*100000000000000^799 ≤ 42893043448609^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267319609 10000000000 42893043448609 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33088547/156250000 : ℝ), (2695531259/5000000000 : ℝ), (5267319609/10000000000 : ℝ)] ![(2575681309159/20000000000000 : ℝ), (22114274992607/50000000000000 : ℝ), (42893043448609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33088547/156250000 : ℝ)|^1055 ≤ (2575681309159/20000000000000 : ℝ)^799
        have hw : |(-33088547/156250000 : ℝ)|=(33088547/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695531259/5000000000 : ℝ)|^1055 ≤ (22114274992607/50000000000000 : ℝ)^799
        have hw : |(2695531259/5000000000 : ℝ)|=(2695531259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267319609/10000000000 : ℝ)|^1055 ≤ (42893043448609/100000000000000 : ℝ)^799
        have hw : |(5267319609/10000000000 : ℝ)|=(5267319609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s8_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344271459/10000000000 : ℝ)*x 0 + (-2180406131/10000000000 : ℝ)*x 1 + (5267319617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344271459/10000000000 : ℝ)^1055 ≤ (21861192898559/50000000000000 : ℝ)^799 := by
    have hnat : (5344271459 : ℕ)^1055*50000000000000^799 ≤ 21861192898559^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344271459 10000000000 21861192898559 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180406131/10000000000 : ℝ)^1055 ≤ (13384570654321/100000000000000 : ℝ)^799 := by
    have hnat : (2180406131 : ℕ)^1055*100000000000000^799 ≤ 13384570654321^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180406131 10000000000 13384570654321 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267319617/10000000000 : ℝ)^1055 ≤ (10723260883657/25000000000000 : ℝ)^799 := by
    have hnat : (5267319617 : ℕ)^1055*25000000000000^799 ≤ 10723260883657^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267319617 10000000000 10723260883657 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344271459/10000000000 : ℝ), (-2180406131/10000000000 : ℝ), (5267319617/10000000000 : ℝ)] ![(21861192898559/50000000000000 : ℝ), (13384570654321/100000000000000 : ℝ), (10723260883657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344271459/10000000000 : ℝ)|^1055 ≤ (21861192898559/50000000000000 : ℝ)^799
        have hw : |(5344271459/10000000000 : ℝ)|=(5344271459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180406131/10000000000 : ℝ)|^1055 ≤ (13384570654321/100000000000000 : ℝ)^799
        have hw : |(-2180406131/10000000000 : ℝ)|=(2180406131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267319617/10000000000 : ℝ)|^1055 ≤ (10723260883657/25000000000000 : ℝ)^799
        have hw : |(5267319617/10000000000 : ℝ)|=(5267319617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s8_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672135751/5000000000 : ℝ)*x 0 + (5267319569/10000000000 : ℝ)*x 1 + (-272550767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672135751/5000000000 : ℝ)^1055 ≤ (21861193130811/50000000000000 : ℝ)^799 := by
    have hnat : (2672135751 : ℕ)^1055*50000000000000^799 ≤ 21861193130811^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672135751 5000000000 21861193130811 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267319569/10000000000 : ℝ)^1055 ≤ (8578608603703/20000000000000 : ℝ)^799 := by
    have hnat : (5267319569 : ℕ)^1055*20000000000000^799 ≤ 8578608603703^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267319569 10000000000 8578608603703 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272550767/1250000000 : ℝ)^1055 ≤ (209133917107/1562500000000 : ℝ)^799 := by
    have hnat : (272550767 : ℕ)^1055*1562500000000^799 ≤ 209133917107^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272550767 1250000000 209133917107 1562500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672135751/5000000000 : ℝ), (5267319569/10000000000 : ℝ), (-272550767/1250000000 : ℝ)] ![(21861193130811/50000000000000 : ℝ), (8578608603703/20000000000000 : ℝ), (209133917107/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672135751/5000000000 : ℝ)|^1055 ≤ (21861193130811/50000000000000 : ℝ)^799
        have hw : |(2672135751/5000000000 : ℝ)|=(2672135751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267319569/10000000000 : ℝ)|^1055 ≤ (8578608603703/20000000000000 : ℝ)^799
        have hw : |(5267319569/10000000000 : ℝ)|=(5267319569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272550767/1250000000 : ℝ)|^1055 ≤ (209133917107/1562500000000 : ℝ)^799
        have hw : |(-272550767/1250000000 : ℝ)|=(272550767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s8_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2175044931/5000000000 : ℝ)*x 0 + (42262199/100000000 : ℝ)*x 1 + (4477483463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175044931/5000000000 : ℝ)^1055 ≤ (33317536327191/100000000000000 : ℝ)^799 := by
    have hnat : (2175044931 : ℕ)^1055*100000000000000^799 ≤ 33317536327191^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175044931 5000000000 33317536327191 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42262199/100000000 : ℝ)^1055 ≤ (1603529513129/5000000000000 : ℝ)^799 := by
    have hnat : (42262199 : ℕ)^1055*5000000000000^799 ≤ 1603529513129^799*100000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42262199 100000000 1603529513129 5000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477483463/10000000000 : ℝ)^1055 ≤ (34611873387917/100000000000000 : ℝ)^799 := by
    have hnat : (4477483463 : ℕ)^1055*100000000000000^799 ≤ 34611873387917^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477483463 10000000000 34611873387917 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175044931/5000000000 : ℝ), (42262199/100000000 : ℝ), (4477483463/10000000000 : ℝ)] ![(33317536327191/100000000000000 : ℝ), (1603529513129/5000000000000 : ℝ), (34611873387917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175044931/5000000000 : ℝ)|^1055 ≤ (33317536327191/100000000000000 : ℝ)^799
        have hw : |(2175044931/5000000000 : ℝ)|=(2175044931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42262199/100000000 : ℝ)|^1055 ≤ (1603529513129/5000000000000 : ℝ)^799
        have hw : |(42262199/100000000 : ℝ)|=(42262199/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477483463/10000000000 : ℝ)|^1055 ≤ (34611873387917/100000000000000 : ℝ)^799
        have hw : |(4477483463/10000000000 : ℝ)|=(4477483463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s8_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-264708953/1250000000 : ℝ)*x 0 + (164613487/312500000 : ℝ)*x 1 + (1347687357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264708953/1250000000 : ℝ)^1055 ≤ (12878443611827/100000000000000 : ℝ)^799 := by
    have hnat : (264708953 : ℕ)^1055*100000000000000^799 ≤ 12878443611827^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264708953 1250000000 12878443611827 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164613487/312500000 : ℝ)^1055 ≤ (42896397940803/100000000000000 : ℝ)^799 := by
    have hnat : (164613487 : ℕ)^1055*100000000000000^799 ≤ 42896397940803^799*312500000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164613487 312500000 42896397940803 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347687357/2500000000 : ℝ)^1055 ≤ (4422515842783/10000000000000 : ℝ)^799 := by
    have hnat : (1347687357 : ℕ)^1055*10000000000000^799 ≤ 4422515842783^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347687357 2500000000 4422515842783 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264708953/1250000000 : ℝ), (164613487/312500000 : ℝ), (1347687357/2500000000 : ℝ)] ![(12878443611827/100000000000000 : ℝ), (42896397940803/100000000000000 : ℝ), (4422515842783/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264708953/1250000000 : ℝ)|^1055 ≤ (12878443611827/100000000000000 : ℝ)^799
        have hw : |(-264708953/1250000000 : ℝ)|=(264708953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164613487/312500000 : ℝ)|^1055 ≤ (42896397940803/100000000000000 : ℝ)^799
        have hw : |(164613487/312500000 : ℝ)|=(164613487/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347687357/2500000000 : ℝ)|^1055 ≤ (4422515842783/10000000000000 : ℝ)^799
        have hw : |(1347687357/2500000000 : ℝ)|=(1347687357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s8_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350099259/10000000000 : ℝ)*x 0 + (559606269/1250000000 : ℝ)*x 1 + (2113427763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350099259/10000000000 : ℝ)^1055 ≤ (8329407839789/25000000000000 : ℝ)^799 := by
    have hnat : (4350099259 : ℕ)^1055*25000000000000^799 ≤ 8329407839789^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350099259 10000000000 8329407839789 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559606269/1250000000 : ℝ)^1055 ≤ (6921081869729/20000000000000 : ℝ)^799 := by
    have hnat : (559606269 : ℕ)^1055*20000000000000^799 ≤ 6921081869729^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559606269 1250000000 6921081869729 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113427763/5000000000 : ℝ)^1055 ≤ (32076959283273/100000000000000 : ℝ)^799 := by
    have hnat : (2113427763 : ℕ)^1055*100000000000000^799 ≤ 32076959283273^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113427763 5000000000 32076959283273 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350099259/10000000000 : ℝ), (559606269/1250000000 : ℝ), (2113427763/5000000000 : ℝ)] ![(8329407839789/25000000000000 : ℝ), (6921081869729/20000000000000 : ℝ), (32076959283273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350099259/10000000000 : ℝ)|^1055 ≤ (8329407839789/25000000000000 : ℝ)^799
        have hw : |(4350099259/10000000000 : ℝ)|=(4350099259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559606269/1250000000 : ℝ)|^1055 ≤ (6921081869729/20000000000000 : ℝ)^799
        have hw : |(559606269/1250000000 : ℝ)|=(559606269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113427763/5000000000 : ℝ)|^1055 ≤ (32076959283273/100000000000000 : ℝ)^799
        have hw : |(2113427763/5000000000 : ℝ)|=(2113427763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2297/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2871/25000 : ℝ) ^ (8439/2048 : ℝ) ≤ (6698612221603389/50000000000000000000 : ℝ) := by
    have hpowers : (2871/25000 : ℝ)^8439 ≤ (6698612221603389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2871 : ℕ)^8439*50000000000000000000^2048 ≤ 6698612221603389^2048*25000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2871 25000 6698612221603389 50000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2871/25000 : ℝ)) (X := (6698612221603389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14107/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (6254402551625119/20000000000000000000 : ℝ) := by
    have hpowers : (14107/100000 : ℝ)^8439 ≤ (6254402551625119/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14107 : ℕ)^8439*20000000000000000000^2048 ≤ 6254402551625119^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14107 100000 6254402551625119 20000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14107/100000 : ℝ)) (X := (6254402551625119/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006698612221603389/25000000000000000000 : ℝ) ≤ (10000650189176449/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (25006698612221603389/25000000000000000000 : ℝ)^2048 ≤ (10000650189176449/10000000000000000 : ℝ)^8439 := by
      have hnat : (25006698612221603389 : ℕ)^2048*10000000000000000^8439 ≤ 10000650189176449^8439*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006698612221603389 25000000000000000000 10000650189176449 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650189176449/10000000000000000 : ℝ)) (X := (25006698612221603389/25000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044669237201332373/100000000000000000000 : ℝ) ≤ (2000216772433017/2000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (100044669237201332373/100000000000000000000 : ℝ)^2048 ≤ (2000216772433017/2000000000000000 : ℝ)^8439 := by
      have hnat : (100044669237201332373 : ℕ)^2048*2000000000000000^8439 ≤ 2000216772433017^8439*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044669237201332373 100000000000000000000 2000216772433017 2000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000216772433017/2000000000000000 : ℝ)) (X := (100044669237201332373/100000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006254402551625119/10000000000000000000 : ℝ) ≤ (10001517535153721/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (10006254402551625119/10000000000000000000 : ℝ)^2048 ≤ (10001517535153721/10000000000000000 : ℝ)^8439 := by
      have hnat : (10006254402551625119 : ℕ)^2048*10000000000000000^8439 ≤ 10001517535153721^8439*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006254402551625119 10000000000000000000 10001517535153721 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001517535153721/10000000000000000 : ℝ)) (X := (10006254402551625119/10000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6698612221603389/50000000000000000000 : ℝ) ≤ ((26221744845006834079/26230000000000000000 : ℝ)+2*(108418247159/65575000000000 : ℝ)*(2871/25000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (26221744845006834079/26230000000000000000 : ℝ)+2*(108418247159/65575000000000 : ℝ)*(2871/25000 : ℝ)=(10000650189176449/10000000000000000 : ℝ) by norm_num, show 1+2*(6698612221603389/50000000000000000000 : ℝ)=(25006698612221603389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6254402551625119/20000000000000000000 : ℝ)+(6698612221603389/50000000000000000000 : ℝ) ≤ ((26221744845006834079/26230000000000000000 : ℝ)+(108418247159/65575000000000 : ℝ)*((14107/100000 : ℝ)+(2871/25000 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (26221744845006834079/26230000000000000000 : ℝ)+(108418247159/65575000000000 : ℝ)*((14107/100000 : ℝ)+(2871/25000 : ℝ))=(2000216772433017/2000000000000000 : ℝ) by norm_num, show 1+(6254402551625119/20000000000000000000 : ℝ)+(6698612221603389/50000000000000000000 : ℝ)=(100044669237201332373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6254402551625119/20000000000000000000 : ℝ) ≤ ((26221744845006834079/26230000000000000000 : ℝ)+2*(108418247159/65575000000000 : ℝ)*(14107/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (26221744845006834079/26230000000000000000 : ℝ)+2*(108418247159/65575000000000 : ℝ)*(14107/100000 : ℝ)=(10001517535153721/10000000000000000 : ℝ) by norm_num, show 1+2*(6254402551625119/20000000000000000000 : ℝ)=(10006254402551625119/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26221744845006834079/26230000000000000000 : ℝ)*(X 1 0+X 2 0)+(108418247159/65575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (26221744845006834079/26230000000000000000 : ℝ)) (alpha := (108418247159/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26221744845006834079/26230000000000000000 : ℝ)*(X 0 1+X 2 1)+(108418247159/65575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (26221744845006834079/26230000000000000000 : ℝ)) (alpha := (108418247159/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26221744845006834079/26230000000000000000 : ℝ)*(X 0 2+X 1 2)+(108418247159/65575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14107/100000 : ℝ)) (c := (26221744845006834079/26230000000000000000 : ℝ)) (alpha := (108418247159/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-33088547/156250000 : ℝ)*X 0 0+(2695531259/5000000000 : ℝ)*X 0 1+(5267319609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344271459/10000000000 : ℝ)*X 1 0+(-2180406131/10000000000 : ℝ)*X 1 1+(5267319617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672135751/5000000000 : ℝ)*X 2 0+(5267319569/10000000000 : ℝ)*X 2 1+(-272550767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175044931/5000000000 : ℝ)*X 0 0+(42262199/100000000 : ℝ)*X 0 1+(4477483463/10000000000 : ℝ)*X 0 2+(2175044931/5000000000 : ℝ)*X 1 0+(42262199/100000000 : ℝ)*X 1 1+(4477483463/10000000000 : ℝ)*X 1 2+(2175044931/5000000000 : ℝ)*X 2 0+(42262199/100000000 : ℝ)*X 2 1+(4477483463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264708953/1250000000 : ℝ)*X 0 0+(164613487/312500000 : ℝ)*X 0 1+(1347687357/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4350099259/10000000000 : ℝ)*X 0 0+(559606269/1250000000 : ℝ)*X 0 1+(2113427763/5000000000 : ℝ)*X 0 2+(4350099259/10000000000 : ℝ)*X 1 0+(559606269/1250000000 : ℝ)*X 1 1+(2113427763/5000000000 : ℝ)*X 1 2+(4350099259/10000000000 : ℝ)*X 2 0+(559606269/1250000000 : ℝ)*X 2 1+(2113427763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4469358906805724464266114741/655750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (642630883/50000000000000 : ℝ)*(base19) + (616239631/50000000000000 : ℝ)*(base23) + (31479091/50000000000000 : ℝ)*(lower2) + (167005793/100000000000000 : ℝ)*(upper3) + (1298059/1562500000000 : ℝ)*(upper5) + (6030633095759193/100000000000000 : ℝ)*(major0) + (6030633095759193/100000000000000 : ℝ)*(major1) + (6030633095759193/100000000000000 : ℝ)*(major2) + (1010163608245877/12500000000000 : ℝ)*(sp0) + (8081343854970541/100000000000000 : ℝ)*(sp1) + (1616268781550609/20000000000000 : ℝ)*(sp2) + (1989950666046693/50000000000000 : ℝ)*(sp3) + (9068566323/25000000000000 : ℝ)*(sp4) + (4873001133/25000000000000 : ℝ)*(sp5) + (1989960412048959/50000000000000 : ℝ)*(f.failure) + (8081345140232307/100000000000000 : ℝ)*(f.sum) + (2722693684397/3278750000000000000000000000 : ℝ)*base65 + (22021944895875261753/2623000000000000000000000000000000 : ℝ)*base68 + (27261991184245261753/2623000000000000000000000000000000 : ℝ)*base70 + (36515396338732261753/2623000000000000000000000000000000 : ℝ)*base72 + (71457533831553/13115000000000000000000000000 : ℝ)*base73 + (42317980754783738247/2623000000000000000000000000000000 : ℝ)*base75 + (30469733531565261753/2623000000000000000000000000000000 : ℝ)*base78 + (23154421969422261753/2623000000000000000000000000000000 : ℝ)*base80 + (18826469433149/6557500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (41906181/5000000000000000000000 : ℝ)*base89 + (41906181/5000000000000000000000 : ℝ)*base91 + (41906181/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1247_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1247_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1247_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1247_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1247_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
