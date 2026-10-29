-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:37.233543+00:00
-- url     : https://prove2.me/submissions/8f0fedaa-768b-4ef5-a7af-7595ab69b94c

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
theorem support_rectangle_w1687_s0_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1407145451/10000000000 : ℝ)*x 0 + (2873162873/5000000000 : ℝ)*x 1 + (4934295373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1407145451/10000000000 : ℝ)^5119 ≤ (8617310560769/100000000000000 : ℝ)^4095 := by
    have hnat : (1407145451 : ℕ)^5119*100000000000000^4095 ≤ 8617310560769^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407145451 10000000000 8617310560769 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2873162873/5000000000 : ℝ)^5119 ≤ (10005829732863/20000000000000 : ℝ)^4095 := by
    have hnat : (2873162873 : ℕ)^5119*20000000000000^4095 ≤ 10005829732863^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2873162873 5000000000 10005829732863 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4934295373/10000000000 : ℝ)^5119 ≤ (20676770381759/50000000000000 : ℝ)^4095 := by
    have hnat : (4934295373 : ℕ)^5119*50000000000000^4095 ≤ 20676770381759^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934295373 10000000000 20676770381759 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1407145451/10000000000 : ℝ), (2873162873/5000000000 : ℝ), (4934295373/10000000000 : ℝ)] ![(8617310560769/100000000000000 : ℝ), (10005829732863/20000000000000 : ℝ), (20676770381759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1407145451/10000000000 : ℝ)|^5119 ≤ (8617310560769/100000000000000 : ℝ)^4095
        have hw : |(-1407145451/10000000000 : ℝ)|=(1407145451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2873162873/5000000000 : ℝ)|^5119 ≤ (10005829732863/20000000000000 : ℝ)^4095
        have hw : |(2873162873/5000000000 : ℝ)|=(2873162873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4934295373/10000000000 : ℝ)|^5119 ≤ (20676770381759/50000000000000 : ℝ)^4095
        have hw : |(4934295373/10000000000 : ℝ)|=(4934295373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338800599/625000000 : ℝ)*x 0 + (-1850354891/10000000000 : ℝ)*x 1 + (1233574131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338800599/625000000 : ℝ)^5119 ≤ (930237730299/2000000000000 : ℝ)^4095 := by
    have hnat : (338800599 : ℕ)^5119*2000000000000^4095 ≤ 930237730299^4095*625000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338800599 625000000 930237730299 2000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850354891/10000000000 : ℝ)^5119 ≤ (2426912128463/20000000000000 : ℝ)^4095 := by
    have hnat : (1850354891 : ℕ)^5119*20000000000000^4095 ≤ 2426912128463^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850354891 10000000000 2426912128463 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233574131/2500000000 : ℝ)^5119 ≤ (41353552822041/100000000000000 : ℝ)^4095 := by
    have hnat : (1233574131 : ℕ)^5119*100000000000000^4095 ≤ 41353552822041^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233574131 2500000000 41353552822041 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338800599/625000000 : ℝ), (-1850354891/10000000000 : ℝ), (1233574131/2500000000 : ℝ)] ![(930237730299/2000000000000 : ℝ), (2426912128463/20000000000000 : ℝ), (41353552822041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338800599/625000000 : ℝ)|^5119 ≤ (930237730299/2000000000000 : ℝ)^4095
        have hw : |(338800599/625000000 : ℝ)|=(338800599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1850354891/10000000000 : ℝ)|^5119 ≤ (2426912128463/20000000000000 : ℝ)^4095
        have hw : |(-1850354891/10000000000 : ℝ)|=(1850354891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1233574131/2500000000 : ℝ)|^5119 ≤ (41353552822041/100000000000000 : ℝ)^4095
        have hw : |(1233574131/2500000000 : ℝ)|=(1233574131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710405837/5000000000 : ℝ)*x 0 + (4934295413/10000000000 : ℝ)*x 1 + (-231294197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710405837/5000000000 : ℝ)^5119 ≤ (23255954465971/50000000000000 : ℝ)^4095 := by
    have hnat : (2710405837 : ℕ)^5119*50000000000000^4095 ≤ 23255954465971^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710405837 5000000000 23255954465971 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4934295413/10000000000 : ℝ)^5119 ≤ (2067677059129/5000000000000 : ℝ)^4095 := by
    have hnat : (4934295413 : ℕ)^5119*5000000000000^4095 ≤ 2067677059129^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934295413 10000000000 2067677059129 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231294197/1250000000 : ℝ)^5119 ≤ (1516818732767/12500000000000 : ℝ)^4095 := by
    have hnat : (231294197 : ℕ)^5119*12500000000000^4095 ≤ 1516818732767^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231294197 1250000000 1516818732767 12500000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710405837/5000000000 : ℝ), (4934295413/10000000000 : ℝ), (-231294197/1250000000 : ℝ)] ![(23255954465971/50000000000000 : ℝ), (2067677059129/5000000000000 : ℝ), (1516818732767/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710405837/5000000000 : ℝ)|^5119 ≤ (23255954465971/50000000000000 : ℝ)^4095
        have hw : |(2710405837/5000000000 : ℝ)|=(2710405837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4934295413/10000000000 : ℝ)|^5119 ≤ (2067677059129/5000000000000 : ℝ)^4095
        have hw : |(4934295413/10000000000 : ℝ)|=(4934295413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231294197/1250000000 : ℝ)|^5119 ≤ (1516818732767/12500000000000 : ℝ)^4095
        have hw : |(-231294197/1250000000 : ℝ)|=(231294197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (253703247/625000000 : ℝ)*x 0 + (1522940303/5000000000 : ℝ)*x 1 + (1055403713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253703247/625000000 : ℝ)^5119 ≤ (32399149203239/100000000000000 : ℝ)^4095 := by
    have hnat : (253703247 : ℕ)^5119*100000000000000^4095 ≤ 32399149203239^4095*625000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253703247 625000000 32399149203239 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522940303/5000000000 : ℝ)^5119 ≤ (1131304669041/5000000000000 : ℝ)^4095 := by
    have hnat : (1522940303 : ℕ)^5119*5000000000000^4095 ≤ 1131304669041^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522940303 5000000000 1131304669041 5000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055403713/2000000000 : ℝ)^5119 ≤ (44974757400967/100000000000000 : ℝ)^4095 := by
    have hnat : (1055403713 : ℕ)^5119*100000000000000^4095 ≤ 44974757400967^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055403713 2000000000 44974757400967 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(253703247/625000000 : ℝ), (1522940303/5000000000 : ℝ), (1055403713/2000000000 : ℝ)] ![(32399149203239/100000000000000 : ℝ), (1131304669041/5000000000000 : ℝ), (44974757400967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(253703247/625000000 : ℝ)|^5119 ≤ (32399149203239/100000000000000 : ℝ)^4095
        have hw : |(253703247/625000000 : ℝ)|=(253703247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1522940303/5000000000 : ℝ)|^5119 ≤ (1131304669041/5000000000000 : ℝ)^4095
        have hw : |(1522940303/5000000000 : ℝ)|=(1522940303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055403713/2000000000 : ℝ)|^5119 ≤ (44974757400967/100000000000000 : ℝ)^4095
        have hw : |(1055403713/2000000000 : ℝ)|=(1055403713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352303163/2500000000 : ℝ)*x 0 + (4954741179/10000000000 : ℝ)*x 1 + (5725169951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352303163/2500000000 : ℝ)^5119 ≤ (2158284643621/25000000000000 : ℝ)^4095 := by
    have hnat : (352303163 : ℕ)^5119*25000000000000^4095 ≤ 2158284643621^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352303163 2500000000 2158284643621 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4954741179/10000000000 : ℝ)^5119 ≤ (4156785337283/10000000000000 : ℝ)^4095 := by
    have hnat : (4954741179 : ℕ)^5119*10000000000000^4095 ≤ 4156785337283^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4954741179 10000000000 4156785337283 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5725169951/10000000000 : ℝ)^5119 ≤ (24899504016007/50000000000000 : ℝ)^4095 := by
    have hnat : (5725169951 : ℕ)^5119*50000000000000^4095 ≤ 24899504016007^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725169951 10000000000 24899504016007 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352303163/2500000000 : ℝ), (4954741179/10000000000 : ℝ), (5725169951/10000000000 : ℝ)] ![(2158284643621/25000000000000 : ℝ), (4156785337283/10000000000000 : ℝ), (24899504016007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352303163/2500000000 : ℝ)|^5119 ≤ (2158284643621/25000000000000 : ℝ)^4095
        have hw : |(-352303163/2500000000 : ℝ)|=(352303163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4954741179/10000000000 : ℝ)|^5119 ≤ (4156785337283/10000000000000 : ℝ)^4095
        have hw : |(4954741179/10000000000 : ℝ)|=(4954741179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5725169951/10000000000 : ℝ)|^5119 ≤ (24899504016007/50000000000000 : ℝ)^4095
        have hw : |(5725169951/10000000000 : ℝ)|=(5725169951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32500899/62500000 : ℝ)*x 0 + (-4237923/40000000 : ℝ)*x 1 + (5725170289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32500899/62500000 : ℝ)^5119 ≤ (70651573939/160000000000 : ℝ)^4095 := by
    have hnat : (32500899 : ℕ)^5119*160000000000^4095 ≤ 70651573939^4095*62500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32500899 62500000 70651573939 160000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237923/40000000 : ℝ)^5119 ≤ (1208750913803/20000000000000 : ℝ)^4095 := by
    have hnat : (4237923 : ℕ)^5119*20000000000000^4095 ≤ 1208750913803^4095*40000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237923 40000000 1208750913803 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5725170289/10000000000 : ℝ)^5119 ≤ (6224876463401/12500000000000 : ℝ)^4095 := by
    have hnat : (5725170289 : ℕ)^5119*12500000000000^4095 ≤ 6224876463401^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725170289 10000000000 6224876463401 12500000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32500899/62500000 : ℝ), (-4237923/40000000 : ℝ), (5725170289/10000000000 : ℝ)] ![(70651573939/160000000000 : ℝ), (1208750913803/20000000000000 : ℝ), (6224876463401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32500899/62500000 : ℝ)|^5119 ≤ (70651573939/160000000000 : ℝ)^4095
        have hw : |(32500899/62500000 : ℝ)|=(32500899/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4237923/40000000 : ℝ)|^5119 ≤ (1208750913803/20000000000000 : ℝ)^4095
        have hw : |(-4237923/40000000 : ℝ)|=(4237923/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5725170289/10000000000 : ℝ)|^5119 ≤ (6224876463401/12500000000000 : ℝ)^4095
        have hw : |(5725170289/10000000000 : ℝ)|=(5725170289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300035981/2500000000 : ℝ)*x 0 + (1431292583/2500000000 : ℝ)*x 1 + (-529740279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300035981/2500000000 : ℝ)^5119 ≤ (4415723460353/10000000000000 : ℝ)^4095 := by
    have hnat : (1300035981 : ℕ)^5119*10000000000000^4095 ≤ 4415723460353^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300035981 2500000000 4415723460353 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1431292583/2500000000 : ℝ)^5119 ≤ (24899506087381/50000000000000 : ℝ)^4095 := by
    have hnat : (1431292583 : ℕ)^5119*50000000000000^4095 ≤ 24899506087381^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431292583 2500000000 24899506087381 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529740279/5000000000 : ℝ)^5119 ≤ (151093829997/2500000000000 : ℝ)^4095 := by
    have hnat : (529740279 : ℕ)^5119*2500000000000^4095 ≤ 151093829997^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529740279 5000000000 151093829997 2500000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300035981/2500000000 : ℝ), (1431292583/2500000000 : ℝ), (-529740279/5000000000 : ℝ)] ![(4415723460353/10000000000000 : ℝ), (24899506087381/50000000000000 : ℝ), (151093829997/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300035981/2500000000 : ℝ)|^5119 ≤ (4415723460353/10000000000000 : ℝ)^4095
        have hw : |(1300035981/2500000000 : ℝ)|=(1300035981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1431292583/2500000000 : ℝ)|^5119 ≤ (24899506087381/50000000000000 : ℝ)^4095
        have hw : |(1431292583/2500000000 : ℝ)|=(1431292583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529740279/5000000000 : ℝ)|^5119 ≤ (151093829997/2500000000000 : ℝ)^4095
        have hw : |(-529740279/5000000000 : ℝ)|=(529740279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s0_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (406493137/1000000000 : ℝ)*x 0 + (522084061/1000000000 : ℝ)*x 1 + (31040071/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406493137/1000000000 : ℝ)^5119 ≤ (16227912562641/50000000000000 : ℝ)^4095 := by
    have hnat : (406493137 : ℕ)^5119*50000000000000^4095 ≤ 16227912562641^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406493137 1000000000 16227912562641 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522084061/1000000000 : ℝ)^5119 ≤ (22188518996479/50000000000000 : ℝ)^4095 := by
    have hnat : (522084061 : ℕ)^5119*50000000000000^4095 ≤ 22188518996479^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522084061 1000000000 22188518996479 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31040071/100000000 : ℝ)^5119 ≤ (23167136862693/100000000000000 : ℝ)^4095 := by
    have hnat : (31040071 : ℕ)^5119*100000000000000^4095 ≤ 23167136862693^4095*100000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31040071 100000000 23167136862693 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(406493137/1000000000 : ℝ), (522084061/1000000000 : ℝ), (31040071/100000000 : ℝ)] ![(16227912562641/50000000000000 : ℝ), (22188518996479/50000000000000 : ℝ), (23167136862693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(406493137/1000000000 : ℝ)|^5119 ≤ (16227912562641/50000000000000 : ℝ)^4095
        have hw : |(406493137/1000000000 : ℝ)|=(406493137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522084061/1000000000 : ℝ)|^5119 ≤ (22188518996479/50000000000000 : ℝ)^4095
        have hw : |(522084061/1000000000 : ℝ)|=(522084061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31040071/100000000 : ℝ)|^5119 ≤ (23167136862693/100000000000000 : ℝ)^4095
        have hw : |(31040071/100000000 : ℝ)|=(31040071/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1333/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11377/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5111/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5111 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5111*1^1024 ≤ 0^1024*1^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5111/1024 : ℝ) ≤ (1032279912296593213/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5111 ≤ (1032279912296593213/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5111*100000000000000000000^1024 ≤ 1032279912296593213^1024*5^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1032279912296593213 100000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1032279912296593213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5111 := by
      have hnat : (1 : ℕ)^1024*1^5111 ≤ 1^5111*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101032279912296593213/100000000000000000000 : ℝ) ≤ (2505149279345181/2500000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (101032279912296593213/100000000000000000000 : ℝ)^1024 ≤ (2505149279345181/2500000000000000 : ℝ)^5111 := by
      have hnat : (101032279912296593213 : ℕ)^1024*2500000000000000^5111 ≤ 2505149279345181^5111*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101032279912296593213 100000000000000000000 2505149279345181 2500000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505149279345181/2500000000000000 : ℝ)) (X := (101032279912296593213/100000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51032279912296593213/50000000000000000000 : ℝ) ≤ (1255149279345181/1250000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (51032279912296593213/50000000000000000000 : ℝ)^1024 ≤ (1255149279345181/1250000000000000 : ℝ)^5111 := by
      have hnat : (51032279912296593213 : ℕ)^1024*1250000000000000^5111 ≤ 1255149279345181^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51032279912296593213 50000000000000000000 1255149279345181 1250000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255149279345181/1250000000000000 : ℝ)) (X := (51032279912296593213/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5149279345181/1000000000000000 : ℝ)*(0 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5149279345181/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1032279912296593213/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5149279345181/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5149279345181/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2505149279345181/2500000000000000 : ℝ) by norm_num, show 1+(1032279912296593213/100000000000000000000 : ℝ)+(0 : ℝ)=(101032279912296593213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1032279912296593213/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5149279345181/1000000000000000 : ℝ)*(2/5 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5149279345181/1000000000000000 : ℝ)*(2/5 : ℝ)=(1255149279345181/1250000000000000 : ℝ) by norm_num, show 1+2*(1032279912296593213/100000000000000000000 : ℝ)=(51032279912296593213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5149279345181/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5149279345181/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5149279345181/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5149279345181/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5149279345181/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5149279345181/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1407145451/10000000000 : ℝ)*X 0 0+(2873162873/5000000000 : ℝ)*X 0 1+(4934295373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338800599/625000000 : ℝ)*X 1 0+(-1850354891/10000000000 : ℝ)*X 1 1+(1233574131/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710405837/5000000000 : ℝ)*X 2 0+(4934295413/10000000000 : ℝ)*X 2 1+(-231294197/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((253703247/625000000 : ℝ)*X 0 0+(1522940303/5000000000 : ℝ)*X 0 1+(1055403713/2000000000 : ℝ)*X 0 2+(253703247/625000000 : ℝ)*X 1 0+(1522940303/5000000000 : ℝ)*X 1 1+(1055403713/2000000000 : ℝ)*X 1 2+(253703247/625000000 : ℝ)*X 2 0+(1522940303/5000000000 : ℝ)*X 2 1+(1055403713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-352303163/2500000000 : ℝ)*X 0 0+(4954741179/10000000000 : ℝ)*X 0 1+(5725169951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((32500899/62500000 : ℝ)*X 1 0+(-4237923/40000000 : ℝ)*X 1 1+(5725170289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1300035981/2500000000 : ℝ)*X 2 0+(1431292583/2500000000 : ℝ)*X 2 1+(-529740279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((406493137/1000000000 : ℝ)*X 0 0+(522084061/1000000000 : ℝ)*X 0 1+(31040071/100000000 : ℝ)*X 0 2+(406493137/1000000000 : ℝ)*X 1 0+(522084061/1000000000 : ℝ)*X 1 1+(31040071/100000000 : ℝ)*X 1 2+(406493137/1000000000 : ℝ)*X 2 0+(522084061/1000000000 : ℝ)*X 2 1+(31040071/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20367951382406734843143/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44237457/100000000000000 : ℝ)*(base1) + (1336636813/100000000000000 : ℝ)*(base19) + (217542781/12500000000000 : ℝ)*(base23) + (2843959/4000000000000 : ℝ)*(base24) + (352170077/100000000000000 : ℝ)*(upper5) + (167970463989299/20000000000000 : ℝ)*(major0) + (167970463989299/20000000000000 : ℝ)*(major1) + (167970463989299/20000000000000 : ℝ)*(major2) + (307871663954549/25000000000000 : ℝ)*(sp0) + (38484229769373/3125000000000 : ℝ)*(sp1) + (615747438907763/50000000000000 : ℝ)*(sp2) + (448205028356367/100000000000000 : ℝ)*(sp3) + (1007767601/10000000000000 : ℝ)*(sp4) + (260646973/10000000000000 : ℝ)*(sp7) + (224103839531777/50000000000000 : ℝ)*(f.failure) + (1231496689256749/100000000000000 : ℝ)*(f.sum) + (13340675538119/10000000000000000000000000000 : ℝ)*base65 + (16887162941881/20000000000000000000000000000 : ℝ)*base68 + (38943331758119/20000000000000000000000000000 : ℝ)*base69 + (24154209058119/20000000000000000000000000000 : ℝ)*base71 + (14496243958119/10000000000000000000000000000 : ℝ)*base73 + (77336934838119/20000000000000000000000000000 : ℝ)*base75 + (56534531058119/20000000000000000000000000000 : ℝ)*base77 + (10177007581881/20000000000000000000000000000 : ℝ)*base80 + (2819557428119/10000000000000000000000000000 : ℝ)*base81 + (5931411/1250000000000000000000 : ℝ)*base89 + (5931411/1250000000000000000000 : ℝ)*base91 + (5931411/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (530080056093915573148851/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2128120769/100000000000000 : ℝ)*(base19) + (2174631867/100000000000000 : ℝ)*(base23) + (18825269/50000000000000 : ℝ)*(base32) + (185031891/50000000000000 : ℝ)*(upper3) + (3794707/1250000000000 : ℝ)*(upper5) + (885191049829643/100000000000000 : ℝ)*(major0) + (885191049829643/100000000000000 : ℝ)*(major1) + (885191049829643/100000000000000 : ℝ)*(major2) + (1844615689/25000000000000 : ℝ)*(sp1) + (7980361469/100000000000000 : ℝ)*(sp2) + (648988973975463/50000000000000 : ℝ)*(sp4) + (648984220683701/50000000000000 : ℝ)*(sp5) + (129796779295759/10000000000000 : ℝ)*(sp6) + (472403760671113/100000000000000 : ℝ)*(sp7) + (472403798321651/100000000000000 : ℝ)*(f.failure) + (648988973975463/50000000000000 : ℝ)*(f.sum) + (11438690100383/50000000000000000000000000000 : ℝ)*base65 + (733280574600383/100000000000000000000000000000 : ℝ)*base67 + (41424049599617/100000000000000000000000000000 : ℝ)*base70 + (42498556399617/100000000000000000000000000000 : ℝ)*base72 + (221956251300383/50000000000000000000000000000 : ℝ)*base73 + (471419519199617/100000000000000000000000000000 : ℝ)*base76 + (365079935400383/100000000000000000000000000000 : ℝ)*base77 + (568532592300383/100000000000000000000000000000 : ℝ)*base79 + (16781553799617/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6074007/2500000000000000000000 : ℝ)*base90 + (6074007/2500000000000000000000 : ℝ)*base92 + (6074007/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1687_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1333/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1687_s1_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1493737831/10000000000 : ℝ)*x 0 + (1377272331/2500000000 : ℝ)*x 1 + (204595449/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1493737831/10000000000 : ℝ)^5119 ≤ (9285227836389/100000000000000 : ℝ)^4095 := by
    have hnat : (1493737831 : ℕ)^5119*100000000000000^4095 ≤ 9285227836389^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493737831 10000000000 9285227836389 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377272331/2500000000 : ℝ)^5119 ≤ (47460680450927/100000000000000 : ℝ)^4095 := by
    have hnat : (1377272331 : ℕ)^5119*100000000000000^4095 ≤ 47460680450927^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377272331 2500000000 47460680450927 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204595449/400000000 : ℝ)^5119 ≤ (10813522924639/25000000000000 : ℝ)^4095 := by
    have hnat : (204595449 : ℕ)^5119*25000000000000^4095 ≤ 10813522924639^4095*400000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204595449 400000000 10813522924639 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1493737831/10000000000 : ℝ), (1377272331/2500000000 : ℝ), (204595449/400000000 : ℝ)] ![(9285227836389/100000000000000 : ℝ), (47460680450927/100000000000000 : ℝ), (10813522924639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1493737831/10000000000 : ℝ)|^5119 ≤ (9285227836389/100000000000000 : ℝ)^4095
        have hw : |(-1493737831/10000000000 : ℝ)|=(1493737831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377272331/2500000000 : ℝ)|^5119 ≤ (47460680450927/100000000000000 : ℝ)^4095
        have hw : |(1377272331/2500000000 : ℝ)|=(1377272331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204595449/400000000 : ℝ)|^5119 ≤ (10813522924639/25000000000000 : ℝ)^4095
        have hw : |(204595449/400000000 : ℝ)|=(204595449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357605851/10000000000 : ℝ)*x 0 + (-339904957/2000000000 : ℝ)*x 1 + (5114886009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357605851/10000000000 : ℝ)^5119 ≤ (45834964985851/100000000000000 : ℝ)^4095 := by
    have hnat : (5357605851 : ℕ)^5119*100000000000000^4095 ≤ 45834964985851^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357605851 10000000000 45834964985851 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339904957/2000000000 : ℝ)^5119 ≤ (85241762323/781250000000 : ℝ)^4095 := by
    have hnat : (339904957 : ℕ)^5119*781250000000^4095 ≤ 85241762323^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339904957 2000000000 85241762323 781250000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5114886009/10000000000 : ℝ)^5119 ≤ (21627044707593/50000000000000 : ℝ)^4095 := by
    have hnat : (5114886009 : ℕ)^5119*50000000000000^4095 ≤ 21627044707593^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114886009 10000000000 21627044707593 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357605851/10000000000 : ℝ), (-339904957/2000000000 : ℝ), (5114886009/10000000000 : ℝ)] ![(45834964985851/100000000000000 : ℝ), (85241762323/781250000000 : ℝ), (21627044707593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357605851/10000000000 : ℝ)|^5119 ≤ (45834964985851/100000000000000 : ℝ)^4095
        have hw : |(5357605851/10000000000 : ℝ)|=(5357605851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339904957/2000000000 : ℝ)|^5119 ≤ (85241762323/781250000000 : ℝ)^4095
        have hw : |(-339904957/2000000000 : ℝ)|=(339904957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5114886009/10000000000 : ℝ)|^5119 ≤ (21627044707593/50000000000000 : ℝ)^4095
        have hw : |(5114886009/10000000000 : ℝ)|=(5114886009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678802577/5000000000 : ℝ)*x 0 + (159840207/312500000 : ℝ)*x 1 + (-212440613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678802577/5000000000 : ℝ)^5119 ≤ (22917478765919/50000000000000 : ℝ)^4095 := by
    have hnat : (2678802577 : ℕ)^5119*50000000000000^4095 ≤ 22917478765919^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678802577 5000000000 22917478765919 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159840207/312500000 : ℝ)^5119 ≤ (43254095916447/100000000000000 : ℝ)^4095 := by
    have hnat : (159840207 : ℕ)^5119*100000000000000^4095 ≤ 43254095916447^4095*312500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159840207 312500000 43254095916447 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212440613/1250000000 : ℝ)^5119 ≤ (5455473266183/50000000000000 : ℝ)^4095 := by
    have hnat : (212440613 : ℕ)^5119*50000000000000^4095 ≤ 5455473266183^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212440613 1250000000 5455473266183 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678802577/5000000000 : ℝ), (159840207/312500000 : ℝ), (-212440613/1250000000 : ℝ)] ![(22917478765919/50000000000000 : ℝ), (43254095916447/100000000000000 : ℝ), (5455473266183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678802577/5000000000 : ℝ)|^5119 ≤ (22917478765919/50000000000000 : ℝ)^4095
        have hw : |(2678802577/5000000000 : ℝ)|=(2678802577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(159840207/312500000 : ℝ)|^5119 ≤ (43254095916447/100000000000000 : ℝ)^4095
        have hw : |(159840207/312500000 : ℝ)|=(159840207/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212440613/1250000000 : ℝ)|^5119 ≤ (5455473266183/50000000000000 : ℝ)^4095
        have hw : |(-212440613/1250000000 : ℝ)|=(212440613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4130803967/10000000000 : ℝ)*x 0 + (903278077/2500000000 : ℝ)*x 1 + (4696225907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4130803967/10000000000 : ℝ)^5119 ≤ (4139327642117/12500000000000 : ℝ)^4095 := by
    have hnat : (4130803967 : ℕ)^5119*12500000000000^4095 ≤ 4139327642117^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130803967 10000000000 4139327642117 12500000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903278077/2500000000 : ℝ)^5119 ≤ (5602151259887/20000000000000 : ℝ)^4095 := by
    have hnat : (903278077 : ℕ)^5119*20000000000000^4095 ≤ 5602151259887^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903278077 2500000000 5602151259887 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696225907/10000000000 : ℝ)^5119 ≤ (7774924509511/20000000000000 : ℝ)^4095 := by
    have hnat : (4696225907 : ℕ)^5119*20000000000000^4095 ≤ 7774924509511^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696225907 10000000000 7774924509511 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4130803967/10000000000 : ℝ), (903278077/2500000000 : ℝ), (4696225907/10000000000 : ℝ)] ![(4139327642117/12500000000000 : ℝ), (5602151259887/20000000000000 : ℝ), (7774924509511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4130803967/10000000000 : ℝ)|^5119 ≤ (4139327642117/12500000000000 : ℝ)^4095
        have hw : |(4130803967/10000000000 : ℝ)|=(4130803967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903278077/2500000000 : ℝ)|^5119 ≤ (5602151259887/20000000000000 : ℝ)^4095
        have hw : |(903278077/2500000000 : ℝ)|=(903278077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4696225907/10000000000 : ℝ)|^5119 ≤ (7774924509511/20000000000000 : ℝ)^4095
        have hw : |(4696225907/10000000000 : ℝ)|=(4696225907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-298794181/2000000000 : ℝ)*x 0 + (2559847287/5000000000 : ℝ)*x 1 + (5504200147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (298794181/2000000000 : ℝ)^5119 ≤ (4643519487543/50000000000000 : ℝ)^4095 := by
    have hnat : (298794181 : ℕ)^5119*50000000000000^4095 ≤ 4643519487543^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298794181 2000000000 4643519487543 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559847287/5000000000 : ℝ)^5119 ≤ (43304927474313/100000000000000 : ℝ)^4095 := by
    have hnat : (2559847287 : ℕ)^5119*100000000000000^4095 ≤ 43304927474313^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559847287 5000000000 43304927474313 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504200147/10000000000 : ℝ)^5119 ≤ (23704016768017/50000000000000 : ℝ)^4095 := by
    have hnat : (5504200147 : ℕ)^5119*50000000000000^4095 ≤ 23704016768017^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504200147 10000000000 23704016768017 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-298794181/2000000000 : ℝ), (2559847287/5000000000 : ℝ), (5504200147/10000000000 : ℝ)] ![(4643519487543/50000000000000 : ℝ), (43304927474313/100000000000000 : ℝ), (23704016768017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-298794181/2000000000 : ℝ)|^5119 ≤ (4643519487543/50000000000000 : ℝ)^4095
        have hw : |(-298794181/2000000000 : ℝ)|=(298794181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559847287/5000000000 : ℝ)|^5119 ≤ (43304927474313/100000000000000 : ℝ)^4095
        have hw : |(2559847287/5000000000 : ℝ)|=(2559847287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504200147/10000000000 : ℝ)|^5119 ≤ (23704016768017/50000000000000 : ℝ)^4095
        have hw : |(5504200147/10000000000 : ℝ)|=(5504200147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262608759/500000000 : ℝ)*x 0 + (-655104689/5000000000 : ℝ)*x 1 + (5504199751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262608759/500000000 : ℝ)^5119 ≤ (8942046545461/20000000000000 : ℝ)^4095 := by
    have hnat : (262608759 : ℕ)^5119*20000000000000^4095 ≤ 8942046545461^4095*500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262608759 500000000 8942046545461 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655104689/5000000000 : ℝ)^5119 ≤ (7881737980367/100000000000000 : ℝ)^4095 := by
    have hnat : (655104689 : ℕ)^5119*100000000000000^4095 ≤ 7881737980367^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655104689 5000000000 7881737980367 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504199751/10000000000 : ℝ)^5119 ≤ (47408029272359/100000000000000 : ℝ)^4095 := by
    have hnat : (5504199751 : ℕ)^5119*100000000000000^4095 ≤ 47408029272359^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504199751 10000000000 47408029272359 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262608759/500000000 : ℝ), (-655104689/5000000000 : ℝ), (5504199751/10000000000 : ℝ)] ![(8942046545461/20000000000000 : ℝ), (7881737980367/100000000000000 : ℝ), (47408029272359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262608759/500000000 : ℝ)|^5119 ≤ (8942046545461/20000000000000 : ℝ)^4095
        have hw : |(262608759/500000000 : ℝ)|=(262608759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655104689/5000000000 : ℝ)|^5119 ≤ (7881737980367/100000000000000 : ℝ)^4095
        have hw : |(-655104689/5000000000 : ℝ)|=(655104689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504199751/10000000000 : ℝ)|^5119 ≤ (47408029272359/100000000000000 : ℝ)^4095
        have hw : |(5504199751/10000000000 : ℝ)|=(5504199751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626087459/5000000000 : ℝ)*x 0 + (5504199989/10000000000 : ℝ)*x 1 + (-1310209409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626087459/5000000000 : ℝ)^5119 ≤ (44710229939257/100000000000000 : ℝ)^4095 := by
    have hnat : (2626087459 : ℕ)^5119*100000000000000^4095 ≤ 44710229939257^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626087459 5000000000 44710229939257 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504199989/10000000000 : ℝ)^5119 ≤ (47408031834871/100000000000000 : ℝ)^4095 := by
    have hnat : (5504199989 : ℕ)^5119*100000000000000^4095 ≤ 47408031834871^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504199989 10000000000 47408031834871 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310209409/10000000000 : ℝ)^5119 ≤ (1970434553371/25000000000000 : ℝ)^4095 := by
    have hnat : (1310209409 : ℕ)^5119*25000000000000^4095 ≤ 1970434553371^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310209409 10000000000 1970434553371 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626087459/5000000000 : ℝ), (5504199989/10000000000 : ℝ), (-1310209409/10000000000 : ℝ)] ![(44710229939257/100000000000000 : ℝ), (47408031834871/100000000000000 : ℝ), (1970434553371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626087459/5000000000 : ℝ)|^5119 ≤ (44710229939257/100000000000000 : ℝ)^4095
        have hw : |(2626087459/5000000000 : ℝ)|=(2626087459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504199989/10000000000 : ℝ)|^5119 ≤ (47408031834871/100000000000000 : ℝ)^4095
        have hw : |(5504199989/10000000000 : ℝ)|=(5504199989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1310209409/10000000000 : ℝ)|^5119 ≤ (1970434553371/25000000000000 : ℝ)^4095
        have hw : |(-1310209409/10000000000 : ℝ)|=(1310209409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s1_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131445451/10000000000 : ℝ)*x 0 + (2341507763/5000000000 : ℝ)*x 1 + (362654329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131445451/10000000000 : ℝ)^5119 ≤ (16560524826173/50000000000000 : ℝ)^4095 := by
    have hnat : (4131445451 : ℕ)^5119*50000000000000^4095 ≤ 16560524826173^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131445451 10000000000 16560524826173 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341507763/5000000000 : ℝ)^5119 ≤ (38737972152167/100000000000000 : ℝ)^4095 := by
    have hnat : (2341507763 : ℕ)^5119*100000000000000^4095 ≤ 38737972152167^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341507763 5000000000 38737972152167 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362654329/1000000000 : ℝ)^5119 ≤ (28140978184979/100000000000000 : ℝ)^4095 := by
    have hnat : (362654329 : ℕ)^5119*100000000000000^4095 ≤ 28140978184979^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362654329 1000000000 28140978184979 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131445451/10000000000 : ℝ), (2341507763/5000000000 : ℝ), (362654329/1000000000 : ℝ)] ![(16560524826173/50000000000000 : ℝ), (38737972152167/100000000000000 : ℝ), (28140978184979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131445451/10000000000 : ℝ)|^5119 ≤ (16560524826173/50000000000000 : ℝ)^4095
        have hw : |(4131445451/10000000000 : ℝ)|=(4131445451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2341507763/5000000000 : ℝ)|^5119 ≤ (38737972152167/100000000000000 : ℝ)^4095
        have hw : |(2341507763/5000000000 : ℝ)|=(2341507763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362654329/1000000000 : ℝ)|^5119 ≤ (28140978184979/100000000000000 : ℝ)^4095
        have hw : |(362654329/1000000000 : ℝ)|=(362654329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1171/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3551/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1333/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1333/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1333/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1333/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1333/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1333/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1333/25000 : ℝ) ^ (5111/1024 : ℝ) ≤ (5527772472639/12500000000000000000 : ℝ) := by
    have hpowers : (1333/25000 : ℝ)^5111 ≤ (5527772472639/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1333 : ℕ)^5111*12500000000000000000^1024 ≤ 5527772472639^1024*25000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1333 25000 5527772472639 12500000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1333/25000 : ℝ)) (X := (5527772472639/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11377/50000 : ℝ) ^ (5111/1024 : ℝ) ≤ (15448262377502421/25000000000000000000 : ℝ) := by
    have hpowers : (11377/50000 : ℝ)^5111 ≤ (15448262377502421/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11377 : ℕ)^5111*25000000000000000000^1024 ≤ 15448262377502421^1024*50000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 50000 15448262377502421 25000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/50000 : ℝ)) (X := (15448262377502421/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250005527772472639/6250000000000000000 : ℝ) ≤ (2500000443000353/2500000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (6250005527772472639/6250000000000000000 : ℝ)^1024 ≤ (2500000443000353/2500000000000000 : ℝ)^5111 := by
      have hnat : (6250005527772472639 : ℕ)^1024*2500000000000000^5111 ≤ 2500000443000353^5111*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250005527772472639 6250000000000000000 2500000443000353 2500000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000443000353/2500000000000000 : ℝ)) (X := (6250005527772472639/6250000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015459317922447699/25000000000000000000 : ℝ) ≤ (1250154827128811/1250000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (25015459317922447699/25000000000000000000 : ℝ)^1024 ≤ (1250154827128811/1250000000000000 : ℝ)^5111 := by
      have hnat : (25015459317922447699 : ℕ)^1024*1250000000000000^5111 ≤ 1250154827128811^5111*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015459317922447699 25000000000000000000 1250154827128811 1250000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250154827128811/1250000000000000 : ℝ)) (X := (25015459317922447699/25000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515448262377502421/12500000000000000000 : ℝ) ≤ (2500618865514891/2500000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (12515448262377502421/12500000000000000000 : ℝ)^1024 ≤ (2500618865514891/2500000000000000 : ℝ)^5111 := by
      have hnat : (12515448262377502421 : ℕ)^1024*2500000000000000^5111 ≤ 2500618865514891^5111*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515448262377502421 12500000000000000000 2500618865514891 2500000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500618865514891/2500000000000000 : ℝ)) (X := (12515448262377502421/12500000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5527772472639/12500000000000000000 : ℝ) ≤ ((28097877605873957/28100000000000000 : ℝ)+2*(309211257269/435550000000000 : ℝ)*(1333/25000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (28097877605873957/28100000000000000 : ℝ)+2*(309211257269/435550000000000 : ℝ)*(1333/25000 : ℝ)=(2500000443000353/2500000000000000 : ℝ) by norm_num, show 1+2*(5527772472639/12500000000000000000 : ℝ)=(6250005527772472639/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15448262377502421/25000000000000000000 : ℝ)+(5527772472639/12500000000000000000 : ℝ) ≤ ((28097877605873957/28100000000000000 : ℝ)+(309211257269/435550000000000 : ℝ)*((11377/50000 : ℝ)+(1333/25000 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (28097877605873957/28100000000000000 : ℝ)+(309211257269/435550000000000 : ℝ)*((11377/50000 : ℝ)+(1333/25000 : ℝ))=(1250154827128811/1250000000000000 : ℝ) by norm_num, show 1+(15448262377502421/25000000000000000000 : ℝ)+(5527772472639/12500000000000000000 : ℝ)=(25015459317922447699/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15448262377502421/25000000000000000000 : ℝ) ≤ ((28097877605873957/28100000000000000 : ℝ)+2*(309211257269/435550000000000 : ℝ)*(11377/50000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (28097877605873957/28100000000000000 : ℝ)+2*(309211257269/435550000000000 : ℝ)*(11377/50000 : ℝ)=(2500618865514891/2500000000000000 : ℝ) by norm_num, show 1+2*(15448262377502421/25000000000000000000 : ℝ)=(12515448262377502421/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28097877605873957/28100000000000000 : ℝ)*(X 1 0+X 2 0)+(309211257269/435550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1333/25000 : ℝ)) (hi := (11377/50000 : ℝ)) (c := (28097877605873957/28100000000000000 : ℝ)) (alpha := (309211257269/435550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28097877605873957/28100000000000000 : ℝ)*(X 0 1+X 2 1)+(309211257269/435550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1333/25000 : ℝ)) (hi := (11377/50000 : ℝ)) (c := (28097877605873957/28100000000000000 : ℝ)) (alpha := (309211257269/435550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28097877605873957/28100000000000000 : ℝ)*(X 0 2+X 1 2)+(309211257269/435550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1333/25000 : ℝ)) (hi := (11377/50000 : ℝ)) (c := (28097877605873957/28100000000000000 : ℝ)) (alpha := (309211257269/435550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1493737831/10000000000 : ℝ)*X 0 0+(1377272331/2500000000 : ℝ)*X 0 1+(204595449/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5357605851/10000000000 : ℝ)*X 1 0+(-339904957/2000000000 : ℝ)*X 1 1+(5114886009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678802577/5000000000 : ℝ)*X 2 0+(159840207/312500000 : ℝ)*X 2 1+(-212440613/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4130803967/10000000000 : ℝ)*X 0 0+(903278077/2500000000 : ℝ)*X 0 1+(4696225907/10000000000 : ℝ)*X 0 2+(4130803967/10000000000 : ℝ)*X 1 0+(903278077/2500000000 : ℝ)*X 1 1+(4696225907/10000000000 : ℝ)*X 1 2+(4130803967/10000000000 : ℝ)*X 2 0+(903278077/2500000000 : ℝ)*X 2 1+(4696225907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-298794181/2000000000 : ℝ)*X 0 0+(2559847287/5000000000 : ℝ)*X 0 1+(5504200147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262608759/500000000 : ℝ)*X 1 0+(-655104689/5000000000 : ℝ)*X 1 1+(5504199751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626087459/5000000000 : ℝ)*X 2 0+(5504199989/10000000000 : ℝ)*X 2 1+(-1310209409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4131445451/10000000000 : ℝ)*X 0 0+(2341507763/5000000000 : ℝ)*X 0 1+(362654329/1000000000 : ℝ)*X 0 2+(4131445451/10000000000 : ℝ)*X 1 0+(2341507763/5000000000 : ℝ)*X 1 1+(362654329/1000000000 : ℝ)*X 1 2+(4131445451/10000000000 : ℝ)*X 2 0+(2341507763/5000000000 : ℝ)*X 2 1+(362654329/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (429561993583516808248424859/43555000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (753475387/50000000000000 : ℝ)*(base19) + (286830187/25000000000000 : ℝ)*(base23) + (257378269/100000000000000 : ℝ)*(upper3) + (15861553/100000000000000 : ℝ)*(upper4) + (59190637/50000000000000 : ℝ)*(upper5) + (1730030681599953/100000000000000 : ℝ)*(major0) + (1730030681599953/100000000000000 : ℝ)*(major1) + (1730030681599953/100000000000000 : ℝ)*(major2) + (126838853287571/5000000000000 : ℝ)*(sp0) + (1268393224745557/50000000000000 : ℝ)*(sp1) + (126839340456057/5000000000000 : ℝ)*(sp2) + (461634177969051/50000000000000 : ℝ)*(sp3) + (2722672617/25000000000000 : ℝ)*(sp4) + (944413859/20000000000000 : ℝ)*(sp7) + (230818269501849/25000000000000 : ℝ)*(f.failure) + (79274623638809/3125000000000 : ℝ)*(f.sum) + (278691789136331/43555000000000000000000000000 : ℝ)*base66 + (59016976613221349/87110000000000000000000000000000 : ℝ)*base68 + (146648161144041349/87110000000000000000000000000000 : ℝ)*base70 + (482013676031671349/87110000000000000000000000000000 : ℝ)*base72 + (16554894710217/21777500000000000000000000000 : ℝ)*base73 + (306855274584341349/87110000000000000000000000000000 : ℝ)*base76 + (93106511763731349/87110000000000000000000000000000 : ℝ)*base78 + (937841076760501349/87110000000000000000000000000000 : ℝ)*base80 + (8276799662503/21777500000000000000000000000 : ℝ)*base82 + (1265493/625000000000000000000 : ℝ)*base90 + (1265493/625000000000000000000 : ℝ)*base92 + (1265493/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (169411645354354835148813/43555000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2214616183/100000000000000 : ℝ)*(base19) + (1132103209/50000000000000 : ℝ)*(base23) + (4194539/1562500000000 : ℝ)*(upper3) + (27899847/50000000000000 : ℝ)*(lower4) + (4570031/100000000000000 : ℝ)*(upper5) + (886821212803773/50000000000000 : ℝ)*(major0) + (886821212803773/50000000000000 : ℝ)*(major1) + (886821212803773/50000000000000 : ℝ)*(major2) + (16033533941/100000000000000 : ℝ)*(sp1) + (19674417211/100000000000000 : ℝ)*(sp2) + (2600737172439153/100000000000000 : ℝ)*(sp4) + (2600718924289029/100000000000000 : ℝ)*(sp5) + (650178808453881/25000000000000 : ℝ)*(sp6) + (946547549122511/100000000000000 : ℝ)*(sp7) + (946547549122511/100000000000000 : ℝ)*(f.failure) + (2600737172439153/100000000000000 : ℝ)*(f.sum) + (5457160278623/2722187500000000000000000000 : ℝ)*base65 + (69406901711333409/43555000000000000000000000000000 : ℝ)*base68 + (183229734884151591/43555000000000000000000000000000 : ℝ)*base69 + (68598210587146591/43555000000000000000000000000000 : ℝ)*base71 + (70120786429603/43555000000000000000000000000 : ℝ)*base73 + (279768963971983409/43555000000000000000000000000000 : ℝ)*base76 + (50176905791321591/43555000000000000000000000000000 : ℝ)*base77 + (209168758853623409/43555000000000000000000000000000 : ℝ)*base80 + (115274569813299/21777500000000000000000000000 : ℝ)*base81 + (9937027/2500000000000000000000 : ℝ)*base90 + (9937027/2500000000000000000000 : ℝ)*base92 + (9937027/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1687_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1171/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1687_s2_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-749704969/5000000000 : ℝ)*x 0 + (685805403/1250000000 : ℝ)*x 1 + (128344119/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749704969/5000000000 : ℝ)^5119 ≤ (9329323894671/100000000000000 : ℝ)^4095 := by
    have hnat : (749704969 : ℕ)^5119*100000000000000^4095 ≤ 9329323894671^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749704969 5000000000 9329323894671 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685805403/1250000000 : ℝ)^5119 ≤ (1475528889467/3125000000000 : ℝ)^4095 := by
    have hnat : (685805403 : ℕ)^5119*3125000000000^4095 ≤ 1475528889467^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685805403 1250000000 1475528889467 3125000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128344119/250000000 : ℝ)^5119 ≤ (43453751629749/100000000000000 : ℝ)^4095 := by
    have hnat : (128344119 : ℕ)^5119*100000000000000^4095 ≤ 43453751629749^4095*250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128344119 250000000 43453751629749 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749704969/5000000000 : ℝ), (685805403/1250000000 : ℝ), (128344119/250000000 : ℝ)] ![(9329323894671/100000000000000 : ℝ), (1475528889467/3125000000000 : ℝ), (43453751629749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749704969/5000000000 : ℝ)|^5119 ≤ (9329323894671/100000000000000 : ℝ)^4095
        have hw : |(-749704969/5000000000 : ℝ)|=(749704969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685805403/1250000000 : ℝ)|^5119 ≤ (1475528889467/3125000000000 : ℝ)^4095
        have hw : |(685805403/1250000000 : ℝ)|=(685805403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128344119/250000000 : ℝ)|^5119 ≤ (43453751629749/100000000000000 : ℝ)^4095
        have hw : |(128344119/250000000 : ℝ)|=(128344119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351544979/10000000000 : ℝ)*x 0 + (-420675093/2500000000 : ℝ)*x 1 + (5133764863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351544979/10000000000 : ℝ)^5119 ≤ (45770156626109/100000000000000 : ℝ)^4095 := by
    have hnat : (5351544979 : ℕ)^5119*100000000000000^4095 ≤ 45770156626109^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351544979 10000000000 45770156626109 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420675093/2500000000 : ℝ)^5119 ≤ (673505665649/6250000000000 : ℝ)^4095 := by
    have hnat : (420675093 : ℕ)^5119*6250000000000^4095 ≤ 673505665649^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420675093 2500000000 673505665649 6250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133764863/10000000000 : ℝ)^5119 ≤ (43453752719581/100000000000000 : ℝ)^4095 := by
    have hnat : (5133764863 : ℕ)^5119*100000000000000^4095 ≤ 43453752719581^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133764863 10000000000 43453752719581 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351544979/10000000000 : ℝ), (-420675093/2500000000 : ℝ), (5133764863/10000000000 : ℝ)] ![(45770156626109/100000000000000 : ℝ), (673505665649/6250000000000 : ℝ), (43453752719581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351544979/10000000000 : ℝ)|^5119 ≤ (45770156626109/100000000000000 : ℝ)^4095
        have hw : |(5351544979/10000000000 : ℝ)|=(5351544979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420675093/2500000000 : ℝ)|^5119 ≤ (673505665649/6250000000000 : ℝ)^4095
        have hw : |(-420675093/2500000000 : ℝ)|=(420675093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133764863/10000000000 : ℝ)|^5119 ≤ (43453752719581/100000000000000 : ℝ)^4095
        have hw : |(5133764863/10000000000 : ℝ)|=(5133764863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070309081/2000000000 : ℝ)*x 0 + (5133764641/10000000000 : ℝ)*x 1 + (-26292189/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070309081/2000000000 : ℝ)^5119 ≤ (11442540295161/25000000000000 : ℝ)^4095 := by
    have hnat : (1070309081 : ℕ)^5119*25000000000000^4095 ≤ 11442540295161^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070309081 2000000000 11442540295161 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133764641/10000000000 : ℝ)^5119 ≤ (21726875185311/50000000000000 : ℝ)^4095 := by
    have hnat : (5133764641 : ℕ)^5119*50000000000000^4095 ≤ 21726875185311^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133764641 10000000000 21726875185311 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26292189/156250000 : ℝ)^5119 ≤ (134701105511/1250000000000 : ℝ)^4095 := by
    have hnat : (26292189 : ℕ)^5119*1250000000000^4095 ≤ 134701105511^4095*156250000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26292189 156250000 134701105511 1250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070309081/2000000000 : ℝ), (5133764641/10000000000 : ℝ), (-26292189/156250000 : ℝ)] ![(11442540295161/25000000000000 : ℝ), (21726875185311/50000000000000 : ℝ), (134701105511/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070309081/2000000000 : ℝ)|^5119 ≤ (11442540295161/25000000000000 : ℝ)^4095
        have hw : |(1070309081/2000000000 : ℝ)|=(1070309081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133764641/10000000000 : ℝ)|^5119 ≤ (21726875185311/50000000000000 : ℝ)^4095
        have hw : |(5133764641/10000000000 : ℝ)|=(5133764641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26292189/156250000 : ℝ)|^5119 ≤ (134701105511/1250000000000 : ℝ)^4095
        have hw : |(-26292189/156250000 : ℝ)|=(26292189/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129223767/312500000 : ℝ)*x 0 + (917437847/2500000000 : ℝ)*x 1 + (579846231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129223767/312500000 : ℝ)^5119 ≤ (33158284689911/100000000000000 : ℝ)^4095 := by
    have hnat : (129223767 : ℕ)^5119*100000000000000^4095 ≤ 33158284689911^4095*312500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129223767 312500000 33158284689911 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917437847/2500000000 : ℝ)^5119 ≤ (446261325773/1562500000000 : ℝ)^4095 := by
    have hnat : (917437847 : ℕ)^5119*1562500000000^4095 ≤ 446261325773^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917437847 2500000000 446261325773 1562500000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579846231/1250000000 : ℝ)^5119 ≤ (2449983389/6400000000 : ℝ)^4095 := by
    have hnat : (579846231 : ℕ)^5119*6400000000^4095 ≤ 2449983389^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579846231 1250000000 2449983389 6400000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129223767/312500000 : ℝ), (917437847/2500000000 : ℝ), (579846231/1250000000 : ℝ)] ![(33158284689911/100000000000000 : ℝ), (446261325773/1562500000000 : ℝ), (2449983389/6400000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129223767/312500000 : ℝ)|^5119 ≤ (33158284689911/100000000000000 : ℝ)^4095
        have hw : |(129223767/312500000 : ℝ)|=(129223767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917437847/2500000000 : ℝ)|^5119 ≤ (446261325773/1562500000000 : ℝ)^4095
        have hw : |(917437847/2500000000 : ℝ)|=(917437847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579846231/1250000000 : ℝ)|^5119 ≤ (2449983389/6400000000 : ℝ)^4095
        have hw : |(579846231/1250000000 : ℝ)|=(579846231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-749788443/5000000000 : ℝ)*x 0 + (1284404203/2500000000 : ℝ)*x 1 + (2741266619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749788443/5000000000 : ℝ)^5119 ≤ (9330622413573/100000000000000 : ℝ)^4095 := by
    have hnat : (749788443 : ℕ)^5119*100000000000000^4095 ≤ 9330622413573^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749788443 5000000000 9330622413573 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284404203/2500000000 : ℝ)^5119 ≤ (8698902724579/20000000000000 : ℝ)^4095 := by
    have hnat : (1284404203 : ℕ)^5119*20000000000000^4095 ≤ 8698902724579^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284404203 2500000000 8698902724579 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741266619/5000000000 : ℝ)^5119 ≤ (47174863953797/100000000000000 : ℝ)^4095 := by
    have hnat : (2741266619 : ℕ)^5119*100000000000000^4095 ≤ 47174863953797^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741266619 5000000000 47174863953797 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749788443/5000000000 : ℝ), (1284404203/2500000000 : ℝ), (2741266619/5000000000 : ℝ)] ![(9330622413573/100000000000000 : ℝ), (8698902724579/20000000000000 : ℝ), (47174863953797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749788443/5000000000 : ℝ)|^5119 ≤ (9330622413573/100000000000000 : ℝ)^4095
        have hw : |(-749788443/5000000000 : ℝ)|=(749788443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284404203/2500000000 : ℝ)|^5119 ≤ (8698902724579/20000000000000 : ℝ)^4095
        have hw : |(1284404203/2500000000 : ℝ)|=(1284404203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741266619/5000000000 : ℝ)|^5119 ≤ (47174863953797/100000000000000 : ℝ)^4095
        have hw : |(2741266619/5000000000 : ℝ)|=(2741266619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328580243/625000000 : ℝ)*x 0 + (-1333932087/10000000000 : ℝ)*x 1 + (5482533263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328580243/625000000 : ℝ)^5119 ≤ (44764603165347/100000000000000 : ℝ)^4095 := by
    have hnat : (328580243 : ℕ)^5119*100000000000000^4095 ≤ 44764603165347^4095*625000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328580243 625000000 44764603165347 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1333932087/10000000000 : ℝ)^5119 ≤ (4030266298349/50000000000000 : ℝ)^4095 := by
    have hnat : (1333932087 : ℕ)^5119*50000000000000^4095 ≤ 4030266298349^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333932087 10000000000 4030266298349 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482533263/10000000000 : ℝ)^5119 ≤ (47174864222703/100000000000000 : ℝ)^4095 := by
    have hnat : (5482533263 : ℕ)^5119*100000000000000^4095 ≤ 47174864222703^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482533263 10000000000 47174864222703 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328580243/625000000 : ℝ), (-1333932087/10000000000 : ℝ), (5482533263/10000000000 : ℝ)] ![(44764603165347/100000000000000 : ℝ), (4030266298349/50000000000000 : ℝ), (47174864222703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328580243/625000000 : ℝ)|^5119 ≤ (44764603165347/100000000000000 : ℝ)^4095
        have hw : |(328580243/625000000 : ℝ)|=(328580243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1333932087/10000000000 : ℝ)|^5119 ≤ (4030266298349/50000000000000 : ℝ)^4095
        have hw : |(-1333932087/10000000000 : ℝ)|=(1333932087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482533263/10000000000 : ℝ)|^5119 ≤ (47174864222703/100000000000000 : ℝ)^4095
        have hw : |(5482533263/10000000000 : ℝ)|=(5482533263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314320991/2500000000 : ℝ)*x 0 + (5482533229/10000000000 : ℝ)*x 1 + (-1333932029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314320991/2500000000 : ℝ)^5119 ≤ (4476460397429/10000000000000 : ℝ)^4095 := by
    have hnat : (1314320991 : ℕ)^5119*10000000000000^4095 ≤ 4476460397429^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314320991 2500000000 4476460397429 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482533229/10000000000 : ℝ)^5119 ≤ (4717486385699/10000000000000 : ℝ)^4095 := by
    have hnat : (5482533229 : ℕ)^5119*10000000000000^4095 ≤ 4717486385699^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482533229 10000000000 4717486385699 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1333932029/10000000000 : ℝ)^5119 ≤ (4030266079291/50000000000000 : ℝ)^4095 := by
    have hnat : (1333932029 : ℕ)^5119*50000000000000^4095 ≤ 4030266079291^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333932029 10000000000 4030266079291 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314320991/2500000000 : ℝ), (5482533229/10000000000 : ℝ), (-1333932029/10000000000 : ℝ)] ![(4476460397429/10000000000000 : ℝ), (4717486385699/10000000000000 : ℝ), (4030266079291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314320991/2500000000 : ℝ)|^5119 ≤ (4476460397429/10000000000000 : ℝ)^4095
        have hw : |(1314320991/2500000000 : ℝ)|=(1314320991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482533229/10000000000 : ℝ)|^5119 ≤ (4717486385699/10000000000000 : ℝ)^4095
        have hw : |(5482533229/10000000000 : ℝ)|=(5482533229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1333932029/10000000000 : ℝ)|^5119 ≤ (4030266079291/50000000000000 : ℝ)^4095
        have hw : |(-1333932029/10000000000 : ℝ)|=(1333932029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_s2_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135619373/10000000000 : ℝ)*x 0 + (578523327/1250000000 : ℝ)*x 1 + (1840246703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135619373/10000000000 : ℝ)^5119 ≤ (33162883948079/100000000000000 : ℝ)^4095 := by
    have hnat : (4135619373 : ℕ)^5119*100000000000000^4095 ≤ 33162883948079^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135619373 10000000000 33162883948079 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578523327/1250000000 : ℝ)^5119 ≤ (38171844934779/100000000000000 : ℝ)^4095 := by
    have hnat : (578523327 : ℕ)^5119*100000000000000^4095 ≤ 38171844934779^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578523327 1250000000 38171844934779 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840246703/5000000000 : ℝ)^5119 ≤ (14332635552423/50000000000000 : ℝ)^4095 := by
    have hnat : (1840246703 : ℕ)^5119*50000000000000^4095 ≤ 14332635552423^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840246703 5000000000 14332635552423 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135619373/10000000000 : ℝ), (578523327/1250000000 : ℝ), (1840246703/5000000000 : ℝ)] ![(33162883948079/100000000000000 : ℝ), (38171844934779/100000000000000 : ℝ), (14332635552423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135619373/10000000000 : ℝ)|^5119 ≤ (33162883948079/100000000000000 : ℝ)^4095
        have hw : |(4135619373/10000000000 : ℝ)|=(4135619373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(578523327/1250000000 : ℝ)|^5119 ≤ (38171844934779/100000000000000 : ℝ)^4095
        have hw : |(578523327/1250000000 : ℝ)|=(578523327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840246703/5000000000 : ℝ)|^5119 ≤ (14332635552423/50000000000000 : ℝ)^4095
        have hw : |(1840246703/5000000000 : ℝ)|=(1840246703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1171/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9779/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8641/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3551/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1171/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3551/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1171/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3551/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1171/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3551/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1171/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3551/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1171/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3551/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1171/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1171/12500 : ℝ) ^ (5111/1024 : ℝ) ≤ (368334733734301/50000000000000000000 : ℝ) := by
    have hpowers : (1171/12500 : ℝ)^5111 ≤ (368334733734301/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1171 : ℕ)^5111*50000000000000000000^1024 ≤ 368334733734301^1024*12500^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1171 12500 368334733734301 50000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1171/12500 : ℝ)) (X := (368334733734301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3551/20000 : ℝ) ^ (5111/1024 : ℝ) ≤ (4478588487178673/25000000000000000000 : ℝ) := by
    have hpowers : (3551/20000 : ℝ)^5111 ≤ (4478588487178673/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3551 : ℕ)^5111*25000000000000000000^1024 ≤ 4478588487178673^1024*20000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3551 20000 4478588487178673 25000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3551/20000 : ℝ)) (X := (4478588487178673/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000368334733734301/25000000000000000000 : ℝ) ≤ (2000005903698619/2000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (25000368334733734301/25000000000000000000 : ℝ)^1024 ≤ (2000005903698619/2000000000000000 : ℝ)^5111 := by
      have hnat : (25000368334733734301 : ℕ)^1024*2000000000000000^5111 ≤ 2000005903698619^5111*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000368334733734301 25000000000000000000 2000005903698619 2000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005903698619/2000000000000000 : ℝ)) (X := (25000368334733734301/25000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009325511708091647/50000000000000000000 : ℝ) ≤ (400014945978421/400000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50009325511708091647/50000000000000000000 : ℝ)^1024 ≤ (400014945978421/400000000000000 : ℝ)^5111 := by
      have hnat : (50009325511708091647 : ℕ)^1024*400000000000000^5111 ≤ 400014945978421^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009325511708091647 50000000000000000000 400014945978421 400000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400014945978421/400000000000000 : ℝ)) (X := (50009325511708091647/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504478588487178673/12500000000000000000 : ℝ) ≤ (2000143556085591/2000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (12504478588487178673/12500000000000000000 : ℝ)^1024 ≤ (2000143556085591/2000000000000000 : ℝ)^5111 := by
      have hnat : (12504478588487178673 : ℕ)^1024*2000000000000000^5111 ≤ 2000143556085591^5111*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504478588487178673 12500000000000000000 2000143556085591 2000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000143556085591/2000000000000000 : ℝ)) (X := (12504478588487178673/12500000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(368334733734301/50000000000000000000 : ℝ) ≤ ((16772759986759163857/16774000000000000000 : ℝ)+2*(34413096743/83870000000000 : ℝ)*(1171/12500 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (16772759986759163857/16774000000000000000 : ℝ)+2*(34413096743/83870000000000 : ℝ)*(1171/12500 : ℝ)=(2000005903698619/2000000000000000 : ℝ) by norm_num, show 1+2*(368334733734301/50000000000000000000 : ℝ)=(25000368334733734301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4478588487178673/25000000000000000000 : ℝ)+(368334733734301/50000000000000000000 : ℝ) ≤ ((16772759986759163857/16774000000000000000 : ℝ)+(34413096743/83870000000000 : ℝ)*((3551/20000 : ℝ)+(1171/12500 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (16772759986759163857/16774000000000000000 : ℝ)+(34413096743/83870000000000 : ℝ)*((3551/20000 : ℝ)+(1171/12500 : ℝ))=(400014945978421/400000000000000 : ℝ) by norm_num, show 1+(4478588487178673/25000000000000000000 : ℝ)+(368334733734301/50000000000000000000 : ℝ)=(50009325511708091647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4478588487178673/25000000000000000000 : ℝ) ≤ ((16772759986759163857/16774000000000000000 : ℝ)+2*(34413096743/83870000000000 : ℝ)*(3551/20000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (16772759986759163857/16774000000000000000 : ℝ)+2*(34413096743/83870000000000 : ℝ)*(3551/20000 : ℝ)=(2000143556085591/2000000000000000 : ℝ) by norm_num, show 1+2*(4478588487178673/25000000000000000000 : ℝ)=(12504478588487178673/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16772759986759163857/16774000000000000000 : ℝ)*(X 1 0+X 2 0)+(34413096743/83870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1171/12500 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (16772759986759163857/16774000000000000000 : ℝ)) (alpha := (34413096743/83870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16772759986759163857/16774000000000000000 : ℝ)*(X 0 1+X 2 1)+(34413096743/83870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1171/12500 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (16772759986759163857/16774000000000000000 : ℝ)) (alpha := (34413096743/83870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16772759986759163857/16774000000000000000 : ℝ)*(X 0 2+X 1 2)+(34413096743/83870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (1171/12500 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (16772759986759163857/16774000000000000000 : ℝ)) (alpha := (34413096743/83870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-749704969/5000000000 : ℝ)*X 0 0+(685805403/1250000000 : ℝ)*X 0 1+(128344119/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351544979/10000000000 : ℝ)*X 1 0+(-420675093/2500000000 : ℝ)*X 1 1+(5133764863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070309081/2000000000 : ℝ)*X 2 0+(5133764641/10000000000 : ℝ)*X 2 1+(-26292189/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((129223767/312500000 : ℝ)*X 0 0+(917437847/2500000000 : ℝ)*X 0 1+(579846231/1250000000 : ℝ)*X 0 2+(129223767/312500000 : ℝ)*X 1 0+(917437847/2500000000 : ℝ)*X 1 1+(579846231/1250000000 : ℝ)*X 1 2+(129223767/312500000 : ℝ)*X 2 0+(917437847/2500000000 : ℝ)*X 2 1+(579846231/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-749788443/5000000000 : ℝ)*X 0 0+(1284404203/2500000000 : ℝ)*X 0 1+(2741266619/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328580243/625000000 : ℝ)*X 1 0+(-1333932087/10000000000 : ℝ)*X 1 1+(5482533263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314320991/2500000000 : ℝ)*X 2 0+(5482533229/10000000000 : ℝ)*X 2 1+(-1333932029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4135619373/10000000000 : ℝ)*X 0 0+(578523327/1250000000 : ℝ)*X 0 1+(1840246703/5000000000 : ℝ)*X 0 2+(4135619373/10000000000 : ℝ)*X 1 0+(578523327/1250000000 : ℝ)*X 1 1+(1840246703/5000000000 : ℝ)*X 1 2+(4135619373/10000000000 : ℝ)*X 2 0+(578523327/1250000000 : ℝ)*X 2 1+(1840246703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (643334609307893937476716143/209675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23691777/4000000000000 : ℝ)*(base19) + (80089447/10000000000000 : ℝ)*(base23) + (9333687/50000000000000 : ℝ)*(upper4) + (25795519/25000000000000 : ℝ)*(upper5) + (483429663103889/25000000000000 : ℝ)*(major0) + (483429663103889/25000000000000 : ℝ)*(major1) + (483429663103889/25000000000000 : ℝ)*(major2) + (708862739882791/25000000000000 : ℝ)*(sp0) + (1417729734339767/50000000000000 : ℝ)*(sp1) + (1417730134490653/50000000000000 : ℝ)*(sp2) + (128996777063411/12500000000000 : ℝ)*(sp3) + (2527586153/25000000000000 : ℝ)*(sp4) + (1008901817/100000000000000 : ℝ)*(sp5) + (1916173151/100000000000000 : ℝ)*(sp7) + (25799403317011/2500000000000 : ℝ)*(f.failure) + (44304079216809/1562500000000 : ℝ)*(f.sum) + (59645703035919/8387000000000000000000000000 : ℝ)*base65 + (5832893397956339873/419350000000000000000000000000000 : ℝ)*base67 + (2455332595487239873/419350000000000000000000000000000 : ℝ)*base69 + (5651075467460389873/419350000000000000000000000000000 : ℝ)*base71 + (11668437250689/1677400000000000000000000000 : ℝ)*base73 + (1335308118318289873/419350000000000000000000000000000 : ℝ)*base75 + (6854855434821589873/419350000000000000000000000000000 : ℝ)*base77 + (1151541960689239873/419350000000000000000000000000000 : ℝ)*base79 + (6020393616809/4193500000000000000000000000 : ℝ)*base81 + (426473/62500000000000000000 : ℝ)*base89 + (426473/62500000000000000000 : ℝ)*base91 + (426473/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5459919989692465209893874783/419350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381762539/20000000000000 : ℝ)*(base19) + (2050457223/100000000000000 : ℝ)*(base23) + (137583277/50000000000000 : ℝ)*(upper3) + (5410071/12500000000000 : ℝ)*(lower4) + (29713437/10000000000000 : ℝ)*(upper5) + (1977223560626827/100000000000000 : ℝ)*(major0) + (1977223560626827/100000000000000 : ℝ)*(major1) + (1977223560626827/100000000000000 : ℝ)*(major2) + (1704229409/10000000000000 : ℝ)*(sp1) + (9006556387/50000000000000 : ℝ)*(sp2) + (1449626549494227/50000000000000 : ℝ)*(sp4) + (724808536970417/25000000000000 : ℝ)*(sp5) + (362404129427307/12500000000000 : ℝ)*(sp6) + (1055193588266547/100000000000000 : ℝ)*(sp7) + (1055193588266547/100000000000000 : ℝ)*(f.failure) + (1449626549494227/50000000000000 : ℝ)*(f.sum) + (16349524268353/8387000000000000000000000000 : ℝ)*base65 + (335408315575191739/1677400000000000000000000000000000 : ℝ)*base67 + (3184808477243591739/1677400000000000000000000000000000 : ℝ)*base69 + (7974907337460191739/1677400000000000000000000000000000 : ℝ)*base71 + (192209454783/167740000000000000000000000 : ℝ)*base73 + (8687941375468791739/1677400000000000000000000000000000 : ℝ)*base75 + (11804237490436191739/1677400000000000000000000000000000 : ℝ)*base77 + (1312150587458808261/1677400000000000000000000000000000 : ℝ)*base80 + (4931543589381/2096750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14676521/2500000000000000000000 : ℝ)*base89 + (14676521/2500000000000000000000 : ℝ)*base91 + (14676521/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1687_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1171/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1687_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1687_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1687_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1687_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1687_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8641/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
