-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1538_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:51.393929+00:00
-- url     : https://prove2.me/submissions/11530b6d-186f-4aee-824d-39a5a0918c2f

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
theorem support_rectangle_w1538_s6_0 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228785103/1250000000 : ℝ)*x 0 + (5429869297/10000000000 : ℝ)*x 1 + (2609423251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228785103/1250000000 : ℝ)^4573 ≤ (11213224294313/100000000000000 : ℝ)^3549 := by
    have hnat : (228785103 : ℕ)^4573*100000000000000^3549 ≤ 11213224294313^3549*1250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228785103 1250000000 11213224294313 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429869297/10000000000 : ℝ)^4573 ≤ (9105370555037/20000000000000 : ℝ)^3549 := by
    have hnat : (5429869297 : ℕ)^4573*20000000000000^3549 ≤ 9105370555037^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429869297 10000000000 9105370555037 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609423251/5000000000 : ℝ)^4573 ≤ (5407490365001/12500000000000 : ℝ)^3549 := by
    have hnat : (2609423251 : ℕ)^4573*12500000000000^3549 ≤ 5407490365001^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609423251 5000000000 5407490365001 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228785103/1250000000 : ℝ), (5429869297/10000000000 : ℝ), (2609423251/5000000000 : ℝ)] ![(11213224294313/100000000000000 : ℝ), (9105370555037/20000000000000 : ℝ), (5407490365001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228785103/1250000000 : ℝ)|^4573 ≤ (11213224294313/100000000000000 : ℝ)^3549
        have hw : |(-228785103/1250000000 : ℝ)|=(228785103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429869297/10000000000 : ℝ)|^4573 ≤ (9105370555037/20000000000000 : ℝ)^3549
        have hw : |(5429869297/10000000000 : ℝ)|=(5429869297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609423251/5000000000 : ℝ)|^4573 ≤ (5407490365001/12500000000000 : ℝ)^3549
        have hw : |(2609423251/5000000000 : ℝ)|=(2609423251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_1 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675053881/5000000000 : ℝ)*x 0 + (-48457519/250000000 : ℝ)*x 1 + (5218846223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675053881/5000000000 : ℝ)^4573 ≤ (44666963762073/100000000000000 : ℝ)^3549 := by
    have hnat : (2675053881 : ℕ)^4573*100000000000000^3549 ≤ 44666963762073^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675053881 5000000000 44666963762073 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48457519/250000000 : ℝ)^4573 ≤ (12073116282771/100000000000000 : ℝ)^3549 := by
    have hnat : (48457519 : ℕ)^4573*100000000000000^3549 ≤ 12073116282771^3549*250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48457519 250000000 12073116282771 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218846223/10000000000 : ℝ)^4573 ≤ (43259919940047/100000000000000 : ℝ)^3549 := by
    have hnat : (5218846223 : ℕ)^4573*100000000000000^3549 ≤ 43259919940047^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218846223 10000000000 43259919940047 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675053881/5000000000 : ℝ), (-48457519/250000000 : ℝ), (5218846223/10000000000 : ℝ)] ![(44666963762073/100000000000000 : ℝ), (12073116282771/100000000000000 : ℝ), (43259919940047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675053881/5000000000 : ℝ)|^4573 ≤ (44666963762073/100000000000000 : ℝ)^3549
        have hw : |(2675053881/5000000000 : ℝ)|=(2675053881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48457519/250000000 : ℝ)|^4573 ≤ (12073116282771/100000000000000 : ℝ)^3549
        have hw : |(-48457519/250000000 : ℝ)|=(48457519/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218846223/10000000000 : ℝ)|^4573 ≤ (43259919940047/100000000000000 : ℝ)^3549
        have hw : |(5218846223/10000000000 : ℝ)|=(5218846223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_2 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350108053/10000000000 : ℝ)*x 0 + (5218845757/10000000000 : ℝ)*x 1 + (-193830099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350108053/10000000000 : ℝ)^4573 ≤ (22333483446281/50000000000000 : ℝ)^3549 := by
    have hnat : (5350108053 : ℕ)^4573*50000000000000^3549 ≤ 22333483446281^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350108053 10000000000 22333483446281 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218845757/10000000000 : ℝ)^4573 ≤ (10814978740691/25000000000000 : ℝ)^3549 := by
    have hnat : (5218845757 : ℕ)^4573*25000000000000^3549 ≤ 10814978740691^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218845757 10000000000 10814978740691 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193830099/1000000000 : ℝ)^4573 ≤ (6036559064363/50000000000000 : ℝ)^3549 := by
    have hnat : (193830099 : ℕ)^4573*50000000000000^3549 ≤ 6036559064363^3549*1000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193830099 1000000000 6036559064363 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350108053/10000000000 : ℝ), (5218845757/10000000000 : ℝ), (-193830099/1000000000 : ℝ)] ![(22333483446281/50000000000000 : ℝ), (10814978740691/25000000000000 : ℝ), (6036559064363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350108053/10000000000 : ℝ)|^4573 ≤ (22333483446281/50000000000000 : ℝ)^3549
        have hw : |(5350108053/10000000000 : ℝ)|=(5350108053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218845757/10000000000 : ℝ)|^4573 ≤ (10814978740691/25000000000000 : ℝ)^3549
        have hw : |(5218845757/10000000000 : ℝ)|=(5218845757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193830099/1000000000 : ℝ)|^4573 ≤ (6036559064363/50000000000000 : ℝ)^3549
        have hw : |(-193830099/1000000000 : ℝ)|=(193830099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_3 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257814799/10000000000 : ℝ)*x 0 + (1004990721/2500000000 : ℝ)*x 1 + (4507256959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257814799/10000000000 : ℝ)^4573 ≤ (33280917496653/100000000000000 : ℝ)^3549 := by
    have hnat : (4257814799 : ℕ)^4573*100000000000000^3549 ≤ 33280917496653^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257814799 10000000000 33280917496653 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004990721/2500000000 : ℝ)^4573 ≤ (30904907315847/100000000000000 : ℝ)^3549 := by
    have hnat : (1004990721 : ℕ)^4573*100000000000000^3549 ≤ 30904907315847^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004990721 2500000000 30904907315847 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507256959/10000000000 : ℝ)^4573 ≤ (35814175172589/100000000000000 : ℝ)^3549 := by
    have hnat : (4507256959 : ℕ)^4573*100000000000000^3549 ≤ 35814175172589^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507256959 10000000000 35814175172589 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257814799/10000000000 : ℝ), (1004990721/2500000000 : ℝ), (4507256959/10000000000 : ℝ)] ![(33280917496653/100000000000000 : ℝ), (30904907315847/100000000000000 : ℝ), (35814175172589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257814799/10000000000 : ℝ)|^4573 ≤ (33280917496653/100000000000000 : ℝ)^3549
        have hw : |(4257814799/10000000000 : ℝ)|=(4257814799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004990721/2500000000 : ℝ)|^4573 ≤ (30904907315847/100000000000000 : ℝ)^3549
        have hw : |(1004990721/2500000000 : ℝ)|=(1004990721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507256959/10000000000 : ℝ)|^4573 ≤ (35814175172589/100000000000000 : ℝ)^3549
        have hw : |(4507256959/10000000000 : ℝ)|=(4507256959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_4 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18303081/100000000 : ℝ)*x 0 + (260996911/500000000 : ℝ)*x 1 + (2714384999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18303081/100000000 : ℝ)^4573 ≤ (1401679952113/12500000000000 : ℝ)^3549 := by
    have hnat : (18303081 : ℕ)^4573*12500000000000^3549 ≤ 1401679952113^3549*100000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18303081 100000000 1401679952113 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260996911/500000000 : ℝ)^4573 ≤ (43271583764303/100000000000000 : ℝ)^3549 := by
    have hnat : (260996911 : ℕ)^4573*100000000000000^3549 ≤ 43271583764303^3549*500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260996911 500000000 43271583764303 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714384999/5000000000 : ℝ)^4573 ≤ (2844686037487/6250000000000 : ℝ)^3549 := by
    have hnat : (2714384999 : ℕ)^4573*6250000000000^3549 ≤ 2844686037487^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714384999 5000000000 2844686037487 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18303081/100000000 : ℝ), (260996911/500000000 : ℝ), (2714384999/5000000000 : ℝ)] ![(1401679952113/12500000000000 : ℝ), (43271583764303/100000000000000 : ℝ), (2844686037487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18303081/100000000 : ℝ)|^4573 ≤ (1401679952113/12500000000000 : ℝ)^3549
        have hw : |(-18303081/100000000 : ℝ)|=(18303081/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260996911/500000000 : ℝ)|^4573 ≤ (43271583764303/100000000000000 : ℝ)^3549
        have hw : |(260996911/500000000 : ℝ)|=(260996911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714384999/5000000000 : ℝ)|^4573 ≤ (2844686037487/6250000000000 : ℝ)^3549
        have hw : |(2714384999/5000000000 : ℝ)|=(2714384999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_5 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294504249/10000000000 : ℝ)*x 0 + (-432094293/2500000000 : ℝ)*x 1 + (5428770029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294504249/10000000000 : ℝ)^4573 ≤ (11017424344517/25000000000000 : ℝ)^3549 := by
    have hnat : (5294504249 : ℕ)^4573*25000000000000^3549 ≤ 11017424344517^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294504249 10000000000 11017424344517 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432094293/2500000000 : ℝ)^4573 ≤ (10415325669473/100000000000000 : ℝ)^3549 := by
    have hnat : (432094293 : ℕ)^4573*100000000000000^3549 ≤ 10415325669473^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432094293 2500000000 10415325669473 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428770029/10000000000 : ℝ)^4573 ≤ (1422343029209/3125000000000 : ℝ)^3549 := by
    have hnat : (5428770029 : ℕ)^4573*3125000000000^3549 ≤ 1422343029209^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428770029 10000000000 1422343029209 3125000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294504249/10000000000 : ℝ), (-432094293/2500000000 : ℝ), (5428770029/10000000000 : ℝ)] ![(11017424344517/25000000000000 : ℝ), (10415325669473/100000000000000 : ℝ), (1422343029209/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294504249/10000000000 : ℝ)|^4573 ≤ (11017424344517/25000000000000 : ℝ)^3549
        have hw : |(5294504249/10000000000 : ℝ)|=(5294504249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432094293/2500000000 : ℝ)|^4573 ≤ (10415325669473/100000000000000 : ℝ)^3549
        have hw : |(-432094293/2500000000 : ℝ)|=(432094293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428770029/10000000000 : ℝ)|^4573 ≤ (1422343029209/3125000000000 : ℝ)^3549
        have hw : |(5428770029/10000000000 : ℝ)|=(5428770029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_6 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294504257/10000000000 : ℝ)*x 0 + (5428770031/10000000000 : ℝ)*x 1 + (-864188579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294504257/10000000000 : ℝ)^4573 ≤ (4406969746387/10000000000000 : ℝ)^3549 := by
    have hnat : (5294504257 : ℕ)^4573*10000000000000^3549 ≤ 4406969746387^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294504257 10000000000 4406969746387 10000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428770031/10000000000 : ℝ)^4573 ≤ (22757488478147/50000000000000 : ℝ)^3549 := by
    have hnat : (5428770031 : ℕ)^4573*50000000000000^3549 ≤ 22757488478147^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428770031 10000000000 22757488478147 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864188579/5000000000 : ℝ)^4573 ≤ (5207662780383/50000000000000 : ℝ)^3549 := by
    have hnat : (864188579 : ℕ)^4573*50000000000000^3549 ≤ 5207662780383^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864188579 5000000000 5207662780383 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294504257/10000000000 : ℝ), (5428770031/10000000000 : ℝ), (-864188579/5000000000 : ℝ)] ![(4406969746387/10000000000000 : ℝ), (22757488478147/50000000000000 : ℝ), (5207662780383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294504257/10000000000 : ℝ)|^4573 ≤ (4406969746387/10000000000000 : ℝ)^3549
        have hw : |(5294504257/10000000000 : ℝ)|=(5294504257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428770031/10000000000 : ℝ)|^4573 ≤ (22757488478147/50000000000000 : ℝ)^3549
        have hw : |(5428770031/10000000000 : ℝ)|=(5428770031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864188579/5000000000 : ℝ)|^4573 ≤ (5207662780383/50000000000000 : ℝ)^3549
        have hw : |(-864188579/5000000000 : ℝ)|=(864188579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_s6_7 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257880423/10000000000 : ℝ)*x 0 + (4504734931/10000000000 : ℝ)*x 1 + (4022502397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257880423/10000000000 : ℝ)^4573 ≤ (650030829/1953125000 : ℝ)^3549 := by
    have hnat : (4257880423 : ℕ)^4573*1953125000^3549 ≤ 650030829^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257880423 10000000000 650030829 1953125000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504734931/10000000000 : ℝ)^4573 ≤ (17894177692133/50000000000000 : ℝ)^3549 := by
    have hnat : (4504734931 : ℕ)^4573*50000000000000^3549 ≤ 17894177692133^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504734931 10000000000 17894177692133 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022502397/10000000000 : ℝ)^4573 ≤ (30930066156063/100000000000000 : ℝ)^3549 := by
    have hnat : (4022502397 : ℕ)^4573*100000000000000^3549 ≤ 30930066156063^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022502397 10000000000 30930066156063 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257880423/10000000000 : ℝ), (4504734931/10000000000 : ℝ), (4022502397/10000000000 : ℝ)] ![(650030829/1953125000 : ℝ), (17894177692133/50000000000000 : ℝ), (30930066156063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257880423/10000000000 : ℝ)|^4573 ≤ (650030829/1953125000 : ℝ)^3549
        have hw : |(4257880423/10000000000 : ℝ)|=(4257880423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504734931/10000000000 : ℝ)|^4573 ≤ (17894177692133/50000000000000 : ℝ)^3549
        have hw : |(4504734931/10000000000 : ℝ)|=(4504734931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022502397/10000000000 : ℝ)|^4573 ≤ (30930066156063/100000000000000 : ℝ)^3549
        have hw : |(4022502397/10000000000 : ℝ)|=(4022502397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1538_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11013/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2753/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2753/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2753/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2753/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2753/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2753/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2753/25000 : ℝ) ^ (4571/1024 : ℝ) ≤ (2642335657224459/50000000000000000000 : ℝ) := by
    have hpowers : (2753/25000 : ℝ)^4571 ≤ (2642335657224459/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2753 : ℕ)^4571*50000000000000000000^1024 ≤ 2642335657224459^1024*25000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2753 25000 2642335657224459 50000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2753/25000 : ℝ)) (X := (2642335657224459/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4571/1024 : ℝ) ≤ (6050778271396197/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4571 ≤ (6050778271396197/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4571*25000000000000000000^1024 ≤ 6050778271396197^1024*20000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 6050778271396197 25000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (6050778271396197/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002642335657224459/25000000000000000000 : ℝ) ≤ (5000118382881761/5000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (25002642335657224459/25000000000000000000 : ℝ)^1024 ≤ (5000118382881761/5000000000000000 : ℝ)^4571 := by
      have hnat : (25002642335657224459 : ℕ)^1024*5000000000000000^4571 ≤ 5000118382881761^4571*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002642335657224459 25000000000000000000 5000118382881761 5000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000118382881761/5000000000000000 : ℝ)) (X := (25002642335657224459/25000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014743892200016853/50000000000000000000 : ℝ) ≤ (10000660512736323/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50014743892200016853/50000000000000000000 : ℝ)^1024 ≤ (10000660512736323/10000000000000000 : ℝ)^4571 := by
      have hnat : (50014743892200016853 : ℕ)^1024*10000000000000000^4571 ≤ 10000660512736323^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014743892200016853 50000000000000000000 10000660512736323 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000660512736323/10000000000000000 : ℝ)) (X := (50014743892200016853/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506050778271396197/12500000000000000000 : ℝ) ≤ (2500271064927281/2500000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (12506050778271396197/12500000000000000000 : ℝ)^1024 ≤ (2500271064927281/2500000000000000 : ℝ)^4571 := by
      have hnat : (12506050778271396197 : ℕ)^1024*2500000000000000^4571 ≤ 2500271064927281^4571*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506050778271396197 12500000000000000000 2500271064927281 2500000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500271064927281/2500000000000000 : ℝ)) (X := (12506050778271396197/12500000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2642335657224459/50000000000000000000 : ℝ) ≤ ((22360863224965632341/22365000000000000000 : ℝ)+2*(423746972801/447300000000000 : ℝ)*(2753/25000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (22360863224965632341/22365000000000000000 : ℝ)+2*(423746972801/447300000000000 : ℝ)*(2753/25000 : ℝ)=(5000118382881761/5000000000000000 : ℝ) by norm_num, show 1+2*(2642335657224459/50000000000000000000 : ℝ)=(25002642335657224459/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6050778271396197/25000000000000000000 : ℝ)+(2642335657224459/50000000000000000000 : ℝ) ≤ ((22360863224965632341/22365000000000000000 : ℝ)+(423746972801/447300000000000 : ℝ)*((3097/20000 : ℝ)+(2753/25000 : ℝ)))^(4571/1024 : ℝ) := by
    rw [show (22360863224965632341/22365000000000000000 : ℝ)+(423746972801/447300000000000 : ℝ)*((3097/20000 : ℝ)+(2753/25000 : ℝ))=(10000660512736323/10000000000000000 : ℝ) by norm_num, show 1+(6050778271396197/25000000000000000000 : ℝ)+(2642335657224459/50000000000000000000 : ℝ)=(50014743892200016853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6050778271396197/25000000000000000000 : ℝ) ≤ ((22360863224965632341/22365000000000000000 : ℝ)+2*(423746972801/447300000000000 : ℝ)*(3097/20000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (22360863224965632341/22365000000000000000 : ℝ)+2*(423746972801/447300000000000 : ℝ)*(3097/20000 : ℝ)=(2500271064927281/2500000000000000 : ℝ) by norm_num, show 1+2*(6050778271396197/25000000000000000000 : ℝ)=(12506050778271396197/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22360863224965632341/22365000000000000000 : ℝ)*(X 1 0+X 2 0)+(423746972801/447300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22360863224965632341/22365000000000000000 : ℝ)) (alpha := (423746972801/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22360863224965632341/22365000000000000000 : ℝ)*(X 0 1+X 2 1)+(423746972801/447300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22360863224965632341/22365000000000000000 : ℝ)) (alpha := (423746972801/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22360863224965632341/22365000000000000000 : ℝ)*(X 0 2+X 1 2)+(423746972801/447300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22360863224965632341/22365000000000000000 : ℝ)) (alpha := (423746972801/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228785103/1250000000 : ℝ)*X 0 0+(5429869297/10000000000 : ℝ)*X 0 1+(2609423251/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675053881/5000000000 : ℝ)*X 1 0+(-48457519/250000000 : ℝ)*X 1 1+(5218846223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350108053/10000000000 : ℝ)*X 2 0+(5218845757/10000000000 : ℝ)*X 2 1+(-193830099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4257814799/10000000000 : ℝ)*X 0 0+(1004990721/2500000000 : ℝ)*X 0 1+(4507256959/10000000000 : ℝ)*X 0 2+(4257814799/10000000000 : ℝ)*X 1 0+(1004990721/2500000000 : ℝ)*X 1 1+(4507256959/10000000000 : ℝ)*X 1 2+(4257814799/10000000000 : ℝ)*X 2 0+(1004990721/2500000000 : ℝ)*X 2 1+(4507256959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18303081/100000000 : ℝ)*X 0 0+(260996911/500000000 : ℝ)*X 0 1+(2714384999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294504249/10000000000 : ℝ)*X 1 0+(-432094293/2500000000 : ℝ)*X 1 1+(5428770029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294504257/10000000000 : ℝ)*X 2 0+(5428770031/10000000000 : ℝ)*X 2 1+(-864188579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257880423/10000000000 : ℝ)*X 0 0+(4504734931/10000000000 : ℝ)*X 0 1+(4022502397/10000000000 : ℝ)*X 0 2+(4257880423/10000000000 : ℝ)*X 1 0+(4504734931/10000000000 : ℝ)*X 1 1+(4022502397/10000000000 : ℝ)*X 1 2+(4257880423/10000000000 : ℝ)*X 2 0+(4504734931/10000000000 : ℝ)*X 2 1+(4022502397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15765322367322306551050189/37275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79046387/10000000000000 : ℝ)*(base19) + (1144552107/100000000000000 : ℝ)*(base23) + (36314941/12500000000000 : ℝ)*(upper2) + (23635161/20000000000000 : ℝ)*(upper3) + (238978709/100000000000000 : ℝ)*(upper4) + (848875540600411/25000000000000 : ℝ)*(major0) + (848875540600411/25000000000000 : ℝ)*(major1) + (1697751081200823/50000000000000 : ℝ)*(major2) + (4738833713256287/100000000000000 : ℝ)*(sp0) + (4738838998505653/100000000000000 : ℝ)*(sp1) + (947767728883483/20000000000000 : ℝ)*(sp2) + (1026077933744863/50000000000000 : ℝ)*(sp3) + (1518928309/25000000000000 : ℝ)*(sp4) + (4327122911/50000000000000 : ℝ)*(sp7) + (513041130433887/25000000000000 : ℝ)*(f.failure) + (4738839788969523/100000000000000 : ℝ)*(f.sum) + (35250841151213/4473000000000000000000000000 : ℝ)*base65 + (9461916247753057849/559125000000000000000000000000000 : ℝ)*base68 + (2984071281676783357/1118250000000000000000000000000000 : ℝ)*base70 + (2589117160839682849/559125000000000000000000000000000 : ℝ)*base72 + (5387768722751/4473000000000000000000000000 : ℝ)*base73 + (6691569908437033357/1118250000000000000000000000000000 : ℝ)*base76 + (597541248371314761/62125000000000000000000000000000 : ℝ)*base78 + (253375219545935239/62125000000000000000000000000000 : ℝ)*base79 + (28827435860887/11182500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (17336963/2500000000000000000000 : ℝ)*base89 + (17336963/2500000000000000000000 : ℝ)*base91 + (32663037/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (377883563045812122305063/109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68129281/12500000000000 : ℝ)*(base19) + (156636649/25000000000000 : ℝ)*(base23) + (22841429/12500000000000 : ℝ)*(lower1) + (81260701/100000000000000 : ℝ)*(upper3) + (30522851/100000000000000 : ℝ)*(lower4) + (34229459/50000000000000 : ℝ)*(upper5) + (1675346277453/48828125000 : ℝ)*(major0) + (1675346277453/48828125000 : ℝ)*(major1) + (1675346277453/48828125000 : ℝ)*(major2) + (1583179501/100000000000000 : ℝ)*(sp2) + (957706728740131/20000000000000 : ℝ)*(sp4) + (4788533098666407/100000000000000 : ℝ)*(sp5) + (2394265716987279/50000000000000 : ℝ)*(sp6) + (2073684593582293/100000000000000 : ℝ)*(sp7) + (2073684593582293/100000000000000 : ℝ)*(f.failure) + (957706728740131/20000000000000 : ℝ)*(f.sum) + (244129225393/105000000000000000000000000 : ℝ)*base65 + (2604077560200323/109375000000000000000000000000 : ℝ)*base67 + (840053047549677/109375000000000000000000000000 : ℝ)*base70 + (4673938648904849/54687500000000000000000000000 : ℝ)*base71 + (618526765307/105000000000000000000000000 : ℝ)*base74 + (3016405331383513/27343750000000000000000000000 : ℝ)*base76 + (319590736345151/54687500000000000000000000000 : ℝ)*base78 + (107617088532651/54687500000000000000000000000 : ℝ)*base80 + (290379546047/105000000000000000000000000 : ℝ)*base82 + (94165857/10000000000000000000000 : ℝ)*base89 + (94165857/10000000000000000000000 : ℝ)*base91 + (94165857/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1538_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1538_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1538_box_0 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1621193587/10000000000 : ℝ)*x 0 + (5400025893/10000000000 : ℝ)*x 1 + (1080005103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621193587/10000000000 : ℝ)^4573 ≤ (9590626301061/100000000000000 : ℝ)^3549 := by
    have hnat : (1621193587 : ℕ)^4573*100000000000000^3549 ≤ 9590626301061^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621193587 10000000000 9590626301061 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400025893/10000000000 : ℝ)^4573 ≤ (22602344438763/50000000000000 : ℝ)^3549 := by
    have hnat : (5400025893 : ℕ)^4573*50000000000000^3549 ≤ 22602344438763^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400025893 10000000000 22602344438763 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080005103/2000000000 : ℝ)^4573 ≤ (2825292800013/6250000000000 : ℝ)^3549 := by
    have hnat : (1080005103 : ℕ)^4573*6250000000000^3549 ≤ 2825292800013^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080005103 2000000000 2825292800013 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1621193587/10000000000 : ℝ), (5400025893/10000000000 : ℝ), (1080005103/2000000000 : ℝ)] ![(9590626301061/100000000000000 : ℝ), (22602344438763/50000000000000 : ℝ), (2825292800013/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1621193587/10000000000 : ℝ)|^4573 ≤ (9590626301061/100000000000000 : ℝ)^3549
        have hw : |(-1621193587/10000000000 : ℝ)|=(1621193587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400025893/10000000000 : ℝ)|^4573 ≤ (22602344438763/50000000000000 : ℝ)^3549
        have hw : |(5400025893/10000000000 : ℝ)|=(5400025893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080005103/2000000000 : ℝ)|^4573 ≤ (2825292800013/6250000000000 : ℝ)^3549
        have hw : |(1080005103/2000000000 : ℝ)|=(1080005103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_1 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65887927/125000000 : ℝ)*x 0 + (-1800308213/10000000000 : ℝ)*x 1 + (5400025973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65887927/125000000 : ℝ)^4573 ≤ (43818134482771/100000000000000 : ℝ)^3549 := by
    have hnat : (65887927 : ℕ)^4573*100000000000000^3549 ≤ 43818134482771^3549*125000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65887927 125000000 43818134482771 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800308213/10000000000 : ℝ)^4573 ≤ (2195435152413/20000000000000 : ℝ)^3549 := by
    have hnat : (1800308213 : ℕ)^4573*20000000000000^3549 ≤ 2195435152413^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800308213 10000000000 2195435152413 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400025973/10000000000 : ℝ)^4573 ≤ (45204689740451/100000000000000 : ℝ)^3549 := by
    have hnat : (5400025973 : ℕ)^4573*100000000000000^3549 ≤ 45204689740451^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400025973 10000000000 45204689740451 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65887927/125000000 : ℝ), (-1800308213/10000000000 : ℝ), (5400025973/10000000000 : ℝ)] ![(43818134482771/100000000000000 : ℝ), (2195435152413/20000000000000 : ℝ), (45204689740451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65887927/125000000 : ℝ)|^4573 ≤ (43818134482771/100000000000000 : ℝ)^3549
        have hw : |(65887927/125000000 : ℝ)|=(65887927/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1800308213/10000000000 : ℝ)|^4573 ≤ (2195435152413/20000000000000 : ℝ)^3549
        have hw : |(-1800308213/10000000000 : ℝ)|=(1800308213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400025973/10000000000 : ℝ)|^4573 ≤ (45204689740451/100000000000000 : ℝ)^3549
        have hw : |(5400025973/10000000000 : ℝ)|=(5400025973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_2 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271034593/10000000000 : ℝ)*x 0 + (5400025599/10000000000 : ℝ)*x 1 + (-225038517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271034593/10000000000 : ℝ)^4573 ≤ (21909069560441/50000000000000 : ℝ)^3549 := by
    have hnat : (5271034593 : ℕ)^4573*50000000000000^3549 ≤ 21909069560441^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271034593 10000000000 21909069560441 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400025599/10000000000 : ℝ)^4573 ≤ (45204685706279/100000000000000 : ℝ)^3549 := by
    have hnat : (5400025599 : ℕ)^4573*100000000000000^3549 ≤ 45204685706279^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400025599 10000000000 45204685706279 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225038517/1250000000 : ℝ)^4573 ≤ (10977175157101/100000000000000 : ℝ)^3549 := by
    have hnat : (225038517 : ℕ)^4573*100000000000000^3549 ≤ 10977175157101^3549*1250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225038517 1250000000 10977175157101 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271034593/10000000000 : ℝ), (5400025599/10000000000 : ℝ), (-225038517/1250000000 : ℝ)] ![(21909069560441/50000000000000 : ℝ), (45204685706279/100000000000000 : ℝ), (10977175157101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271034593/10000000000 : ℝ)|^4573 ≤ (21909069560441/50000000000000 : ℝ)^3549
        have hw : |(5271034593/10000000000 : ℝ)|=(5271034593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400025599/10000000000 : ℝ)|^4573 ≤ (45204685706279/100000000000000 : ℝ)^3549
        have hw : |(5400025599/10000000000 : ℝ)|=(5400025599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225038517/1250000000 : ℝ)|^4573 ≤ (10977175157101/100000000000000 : ℝ)^3549
        have hw : |(-225038517/1250000000 : ℝ)|=(225038517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_3 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (222987423/500000000 : ℝ)*x 0 + (4163669149/10000000000 : ℝ)*x 1 + (130114667/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222987423/500000000 : ℝ)^4573 ≤ (17664249619761/50000000000000 : ℝ)^3549 := by
    have hnat : (222987423 : ℕ)^4573*50000000000000^3549 ≤ 17664249619761^3549*500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222987423 500000000 17664249619761 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163669149/10000000000 : ℝ)^4573 ≤ (32335749398769/100000000000000 : ℝ)^3549 := by
    have hnat : (4163669149 : ℕ)^4573*100000000000000^3549 ≤ 32335749398769^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163669149 10000000000 32335749398769 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130114667/312500000 : ℝ)^4573 ≤ (258686010801/800000000000 : ℝ)^3549 := by
    have hnat : (130114667 : ℕ)^4573*800000000000^3549 ≤ 258686010801^3549*312500000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130114667 312500000 258686010801 800000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222987423/500000000 : ℝ), (4163669149/10000000000 : ℝ), (130114667/312500000 : ℝ)] ![(17664249619761/50000000000000 : ℝ), (32335749398769/100000000000000 : ℝ), (258686010801/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222987423/500000000 : ℝ)|^4573 ≤ (17664249619761/50000000000000 : ℝ)^3549
        have hw : |(222987423/500000000 : ℝ)|=(222987423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163669149/10000000000 : ℝ)|^4573 ≤ (32335749398769/100000000000000 : ℝ)^3549
        have hw : |(4163669149/10000000000 : ℝ)|=(4163669149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130114667/312500000 : ℝ)|^4573 ≤ (258686010801/800000000000 : ℝ)^3549
        have hw : |(130114667/312500000 : ℝ)|=(130114667/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_4 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044784771/10000000000 : ℝ)*x 0 + (1311093739/2500000000 : ℝ)*x 1 + (209775017/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044784771/10000000000 : ℝ)^4573 ≤ (808402050509/6250000000000 : ℝ)^3549 := by
    have hnat : (2044784771 : ℕ)^4573*6250000000000^3549 ≤ 808402050509^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044784771 10000000000 808402050509 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311093739/2500000000 : ℝ)^4573 ≤ (1360399408811/3125000000000 : ℝ)^3549 := by
    have hnat : (1311093739 : ℕ)^4573*3125000000000^3549 ≤ 1360399408811^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311093739 2500000000 1360399408811 3125000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209775017/400000000 : ℝ)^4573 ≤ (8706557219667/20000000000000 : ℝ)^3549 := by
    have hnat : (209775017 : ℕ)^4573*20000000000000^3549 ≤ 8706557219667^3549*400000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209775017 400000000 8706557219667 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044784771/10000000000 : ℝ), (1311093739/2500000000 : ℝ), (209775017/400000000 : ℝ)] ![(808402050509/6250000000000 : ℝ), (1360399408811/3125000000000 : ℝ), (8706557219667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044784771/10000000000 : ℝ)|^4573 ≤ (808402050509/6250000000000 : ℝ)^3549
        have hw : |(-2044784771/10000000000 : ℝ)|=(2044784771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311093739/2500000000 : ℝ)|^4573 ≤ (1360399408811/3125000000000 : ℝ)^3549
        have hw : |(1311093739/2500000000 : ℝ)|=(1311093739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209775017/400000000 : ℝ)|^4573 ≤ (8706557219667/20000000000000 : ℝ)^3549
        have hw : |(209775017/400000000 : ℝ)|=(209775017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_5 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689593331/5000000000 : ℝ)*x 0 + (-932445827/5000000000 : ℝ)*x 1 + (2622187349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689593331/5000000000 : ℝ)^4573 ≤ (22490015291839/50000000000000 : ℝ)^3549 := by
    have hnat : (2689593331 : ℕ)^4573*50000000000000^3549 ≤ 22490015291839^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689593331 5000000000 22490015291839 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932445827/5000000000 : ℝ)^4573 ≤ (5743595541591/50000000000000 : ℝ)^3549 := by
    have hnat : (932445827 : ℕ)^4573*50000000000000^3549 ≤ 5743595541591^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932445827 5000000000 5743595541591 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622187349/5000000000 : ℝ)^4573 ≤ (21766389161203/50000000000000 : ℝ)^3549 := by
    have hnat : (2622187349 : ℕ)^4573*50000000000000^3549 ≤ 21766389161203^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622187349 5000000000 21766389161203 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689593331/5000000000 : ℝ), (-932445827/5000000000 : ℝ), (2622187349/5000000000 : ℝ)] ![(22490015291839/50000000000000 : ℝ), (5743595541591/50000000000000 : ℝ), (21766389161203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689593331/5000000000 : ℝ)|^4573 ≤ (22490015291839/50000000000000 : ℝ)^3549
        have hw : |(2689593331/5000000000 : ℝ)|=(2689593331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-932445827/5000000000 : ℝ)|^4573 ≤ (5743595541591/50000000000000 : ℝ)^3549
        have hw : |(-932445827/5000000000 : ℝ)|=(932445827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622187349/5000000000 : ℝ)|^4573 ≤ (21766389161203/50000000000000 : ℝ)^3549
        have hw : |(2622187349/5000000000 : ℝ)|=(2622187349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_6 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689593223/5000000000 : ℝ)*x 0 + (5244375447/10000000000 : ℝ)*x 1 + (-932445469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689593223/5000000000 : ℝ)^4573 ≤ (44980028256379/100000000000000 : ℝ)^3549 := by
    have hnat : (2689593223 : ℕ)^4573*100000000000000^3549 ≤ 44980028256379^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689593223 5000000000 44980028256379 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244375447/10000000000 : ℝ)^4573 ≤ (8706557266729/20000000000000 : ℝ)^3549 := by
    have hnat : (5244375447 : ℕ)^4573*20000000000000^3549 ≤ 8706557266729^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244375447 10000000000 8706557266729 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932445469/5000000000 : ℝ)^4573 ≤ (11487185400303/100000000000000 : ℝ)^3549 := by
    have hnat : (932445469 : ℕ)^4573*100000000000000^3549 ≤ 11487185400303^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932445469 5000000000 11487185400303 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689593223/5000000000 : ℝ), (5244375447/10000000000 : ℝ), (-932445469/5000000000 : ℝ)] ![(44980028256379/100000000000000 : ℝ), (8706557266729/20000000000000 : ℝ), (11487185400303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689593223/5000000000 : ℝ)|^4573 ≤ (44980028256379/100000000000000 : ℝ)^3549
        have hw : |(2689593223/5000000000 : ℝ)|=(2689593223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244375447/10000000000 : ℝ)|^4573 ≤ (8706557266729/20000000000000 : ℝ)^3549
        have hw : |(5244375447/10000000000 : ℝ)|=(5244375447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-932445469/5000000000 : ℝ)|^4573 ≤ (11487185400303/100000000000000 : ℝ)^3549
        have hw : |(-932445469/5000000000 : ℝ)|=(932445469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_7 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4053340347/10000000000 : ℝ)*x 0 + (2183371551/5000000000 : ℝ)*x 1 + (4366741397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4053340347/10000000000 : ℝ)^4573 ≤ (15617970736349/50000000000000 : ℝ)^3549 := by
    have hnat : (4053340347 : ℕ)^4573*50000000000000^3549 ≤ 15617970736349^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053340347 10000000000 15617970736349 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183371551/5000000000 : ℝ)^4573 ≤ (8595509476463/25000000000000 : ℝ)^3549 := by
    have hnat : (2183371551 : ℕ)^4573*25000000000000^3549 ≤ 8595509476463^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183371551 5000000000 8595509476463 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4366741397/10000000000 : ℝ)^4573 ≤ (17191010303973/50000000000000 : ℝ)^3549 := by
    have hnat : (4366741397 : ℕ)^4573*50000000000000^3549 ≤ 17191010303973^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366741397 10000000000 17191010303973 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4053340347/10000000000 : ℝ), (2183371551/5000000000 : ℝ), (4366741397/10000000000 : ℝ)] ![(15617970736349/50000000000000 : ℝ), (8595509476463/25000000000000 : ℝ), (17191010303973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4053340347/10000000000 : ℝ)|^4573 ≤ (15617970736349/50000000000000 : ℝ)^3549
        have hw : |(4053340347/10000000000 : ℝ)|=(4053340347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2183371551/5000000000 : ℝ)|^4573 ≤ (8595509476463/25000000000000 : ℝ)^3549
        have hw : |(2183371551/5000000000 : ℝ)|=(2183371551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4366741397/10000000000 : ℝ)|^4573 ≤ (17191010303973/50000000000000 : ℝ)^3549
        have hw : |(4366741397/10000000000 : ℝ)|=(4366741397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_8 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391028149/2000000000 : ℝ)*x 0 + (1027010297/2000000000 : ℝ)*x 1 + (5420398433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391028149/2000000000 : ℝ)^4573 ≤ (12208441272007/100000000000000 : ℝ)^3549 := by
    have hnat : (391028149 : ℕ)^4573*100000000000000^3549 ≤ 12208441272007^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391028149 2000000000 12208441272007 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027010297/2000000000 : ℝ)^4573 ≤ (10591750193589/25000000000000 : ℝ)^3549 := by
    have hnat : (1027010297 : ℕ)^4573*25000000000000^3549 ≤ 10591750193589^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027010297 2000000000 10591750193589 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420398433/10000000000 : ℝ)^4573 ≤ (9084911587641/20000000000000 : ℝ)^3549 := by
    have hnat : (5420398433 : ℕ)^4573*20000000000000^3549 ≤ 9084911587641^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420398433 10000000000 9084911587641 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391028149/2000000000 : ℝ), (1027010297/2000000000 : ℝ), (5420398433/10000000000 : ℝ)] ![(12208441272007/100000000000000 : ℝ), (10591750193589/25000000000000 : ℝ), (9084911587641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391028149/2000000000 : ℝ)|^4573 ≤ (12208441272007/100000000000000 : ℝ)^3549
        have hw : |(-391028149/2000000000 : ℝ)|=(391028149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027010297/2000000000 : ℝ)|^4573 ≤ (10591750193589/25000000000000 : ℝ)^3549
        have hw : |(1027010297/2000000000 : ℝ)|=(1027010297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420398433/10000000000 : ℝ)|^4573 ≤ (9084911587641/20000000000000 : ℝ)^3549
        have hw : |(5420398433/10000000000 : ℝ)|=(5420398433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_9 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256874001/10000000000 : ℝ)*x 0 + (-1791615489/10000000000 : ℝ)*x 1 + (5420398329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256874001/10000000000 : ℝ)^4573 ≤ (10916628931521/25000000000000 : ℝ)^3549 := by
    have hnat : (5256874001 : ℕ)^4573*25000000000000^3549 ≤ 10916628931521^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256874001 10000000000 10916628931521 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791615489/10000000000 : ℝ)^4573 ≤ (1363615932071/12500000000000 : ℝ)^3549 := by
    have hnat : (1791615489 : ℕ)^4573*12500000000000^3549 ≤ 1363615932071^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791615489 10000000000 1363615932071 12500000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420398329/10000000000 : ℝ)^4573 ≤ (45424556815183/100000000000000 : ℝ)^3549 := by
    have hnat : (5420398329 : ℕ)^4573*100000000000000^3549 ≤ 45424556815183^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420398329 10000000000 45424556815183 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256874001/10000000000 : ℝ), (-1791615489/10000000000 : ℝ), (5420398329/10000000000 : ℝ)] ![(10916628931521/25000000000000 : ℝ), (1363615932071/12500000000000 : ℝ), (45424556815183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256874001/10000000000 : ℝ)|^4573 ≤ (10916628931521/25000000000000 : ℝ)^3549
        have hw : |(5256874001/10000000000 : ℝ)|=(5256874001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791615489/10000000000 : ℝ)|^4573 ≤ (1363615932071/12500000000000 : ℝ)^3549
        have hw : |(-1791615489/10000000000 : ℝ)|=(1791615489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420398329/10000000000 : ℝ)|^4573 ≤ (45424556815183/100000000000000 : ℝ)^3549
        have hw : |(5420398329/10000000000 : ℝ)|=(5420398329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_10 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628436777/5000000000 : ℝ)*x 0 + (5420398837/10000000000 : ℝ)*x 1 + (-895807699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628436777/5000000000 : ℝ)^4573 ≤ (21833255470863/50000000000000 : ℝ)^3549 := by
    have hnat : (2628436777 : ℕ)^4573*50000000000000^3549 ≤ 21833255470863^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628436777 5000000000 21833255470863 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420398837/10000000000 : ℝ)^4573 ≤ (45424562300711/100000000000000 : ℝ)^3549 := by
    have hnat : (5420398837 : ℕ)^4573*100000000000000^3549 ≤ 45424562300711^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420398837 10000000000 45424562300711 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895807699/5000000000 : ℝ)^4573 ≤ (681807921413/6250000000000 : ℝ)^3549 := by
    have hnat : (895807699 : ℕ)^4573*6250000000000^3549 ≤ 681807921413^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895807699 5000000000 681807921413 6250000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628436777/5000000000 : ℝ), (5420398837/10000000000 : ℝ), (-895807699/5000000000 : ℝ)] ![(21833255470863/50000000000000 : ℝ), (45424562300711/100000000000000 : ℝ), (681807921413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628436777/5000000000 : ℝ)|^4573 ≤ (21833255470863/50000000000000 : ℝ)^3549
        have hw : |(2628436777/5000000000 : ℝ)|=(2628436777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420398837/10000000000 : ℝ)|^4573 ≤ (45424562300711/100000000000000 : ℝ)^3549
        have hw : |(5420398837/10000000000 : ℝ)|=(5420398837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-895807699/5000000000 : ℝ)|^4573 ≤ (681807921413/6250000000000 : ℝ)^3549
        have hw : |(-895807699/5000000000 : ℝ)|=(895807699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_11 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140993581/312500000 : ℝ)*x 0 + (129283013/312500000 : ℝ)*x 1 + (827411153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140993581/312500000 : ℝ)^4573 ≤ (35860640634811/100000000000000 : ℝ)^3549 := by
    have hnat : (140993581 : ℕ)^4573*100000000000000^3549 ≤ 35860640634811^3549*312500000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140993581 312500000 35860640634811 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129283013/312500000 : ℝ)^4573 ≤ (32069682933203/100000000000000 : ℝ)^3549 := by
    have hnat : (129283013 : ℕ)^4573*100000000000000^3549 ≤ 32069682933203^3549*312500000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129283013 312500000 32069682933203 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827411153/2000000000 : ℝ)^4573 ≤ (32069676430717/100000000000000 : ℝ)^3549 := by
    have hnat : (827411153 : ℕ)^4573*100000000000000^3549 ≤ 32069676430717^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827411153 2000000000 32069676430717 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140993581/312500000 : ℝ), (129283013/312500000 : ℝ), (827411153/2000000000 : ℝ)] ![(35860640634811/100000000000000 : ℝ), (32069682933203/100000000000000 : ℝ), (32069676430717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140993581/312500000 : ℝ)|^4573 ≤ (35860640634811/100000000000000 : ℝ)^3549
        have hw : |(140993581/312500000 : ℝ)|=(140993581/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129283013/312500000 : ℝ)|^4573 ≤ (32069682933203/100000000000000 : ℝ)^3549
        have hw : |(129283013/312500000 : ℝ)|=(129283013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827411153/2000000000 : ℝ)|^4573 ≤ (32069676430717/100000000000000 : ℝ)^3549
        have hw : |(827411153/2000000000 : ℝ)|=(827411153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_12 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1710652059/10000000000 : ℝ)*x 0 + (2752960131/5000000000 : ℝ)*x 1 + (5229333057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1710652059/10000000000 : ℝ)^4573 ≤ (160592157339/1562500000000 : ℝ)^3549 := by
    have hnat : (1710652059 : ℕ)^4573*1562500000000^3549 ≤ 160592157339^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710652059 10000000000 160592157339 1562500000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752960131/5000000000 : ℝ)^4573 ≤ (23175070534889/50000000000000 : ℝ)^3549 := by
    have hnat : (2752960131 : ℕ)^4573*50000000000000^3549 ≤ 23175070534889^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752960131 5000000000 23175070534889 50000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229333057/10000000000 : ℝ)^4573 ≤ (8674392169943/20000000000000 : ℝ)^3549 := by
    have hnat : (5229333057 : ℕ)^4573*20000000000000^3549 ≤ 8674392169943^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229333057 10000000000 8674392169943 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1710652059/10000000000 : ℝ), (2752960131/5000000000 : ℝ), (5229333057/10000000000 : ℝ)] ![(160592157339/1562500000000 : ℝ), (23175070534889/50000000000000 : ℝ), (8674392169943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1710652059/10000000000 : ℝ)|^4573 ≤ (160592157339/1562500000000 : ℝ)^3549
        have hw : |(-1710652059/10000000000 : ℝ)|=(1710652059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752960131/5000000000 : ℝ)|^4573 ≤ (23175070534889/50000000000000 : ℝ)^3549
        have hw : |(2752960131/5000000000 : ℝ)|=(2752960131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229333057/10000000000 : ℝ)|^4573 ≤ (8674392169943/20000000000000 : ℝ)^3549
        have hw : |(5229333057/10000000000 : ℝ)|=(5229333057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_13 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389638927/10000000000 : ℝ)*x 0 + (-374191573/2000000000 : ℝ)*x 1 + (130733321/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389638927/10000000000 : ℝ)^4573 ≤ (352286565477/781250000000 : ℝ)^3549 := by
    have hnat : (5389638927 : ℕ)^4573*781250000000^3549 ≤ 352286565477^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389638927 10000000000 352286565477 781250000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374191573/2000000000 : ℝ)^4573 ≤ (11535361072867/100000000000000 : ℝ)^3549 := by
    have hnat : (374191573 : ℕ)^4573*100000000000000^3549 ≤ 11535361072867^3549*2000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374191573 2000000000 11535361072867 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130733321/250000000 : ℝ)^4573 ≤ (69395133649/160000000000 : ℝ)^3549 := by
    have hnat : (130733321 : ℕ)^4573*160000000000^3549 ≤ 69395133649^3549*250000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130733321 250000000 69395133649 160000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389638927/10000000000 : ℝ), (-374191573/2000000000 : ℝ), (130733321/250000000 : ℝ)] ![(352286565477/781250000000 : ℝ), (11535361072867/100000000000000 : ℝ), (69395133649/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389638927/10000000000 : ℝ)|^4573 ≤ (352286565477/781250000000 : ℝ)^3549
        have hw : |(5389638927/10000000000 : ℝ)|=(5389638927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374191573/2000000000 : ℝ)|^4573 ≤ (11535361072867/100000000000000 : ℝ)^3549
        have hw : |(-374191573/2000000000 : ℝ)|=(374191573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130733321/250000000 : ℝ)|^4573 ≤ (69395133649/160000000000 : ℝ)^3549
        have hw : |(130733321/250000000 : ℝ)|=(130733321/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_14 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389638707/10000000000 : ℝ)*x 0 + (2614666461/5000000000 : ℝ)*x 1 + (-1870958053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389638707/10000000000 : ℝ)^4573 ≤ (11273169502333/25000000000000 : ℝ)^3549 := by
    have hnat : (5389638707 : ℕ)^4573*25000000000000^3549 ≤ 11273169502333^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389638707 10000000000 11273169502333 25000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614666461/5000000000 : ℝ)^4573 ≤ (43371959406963/100000000000000 : ℝ)^3549 := by
    have hnat : (2614666461 : ℕ)^4573*100000000000000^3549 ≤ 43371959406963^3549*5000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614666461 5000000000 43371959406963 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870958053/10000000000 : ℝ)^4573 ≤ (11535362566419/100000000000000 : ℝ)^3549 := by
    have hnat : (1870958053 : ℕ)^4573*100000000000000^3549 ≤ 11535362566419^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870958053 10000000000 11535362566419 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389638707/10000000000 : ℝ), (2614666461/5000000000 : ℝ), (-1870958053/10000000000 : ℝ)] ![(11273169502333/25000000000000 : ℝ), (43371959406963/100000000000000 : ℝ), (11535362566419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389638707/10000000000 : ℝ)|^4573 ≤ (11273169502333/25000000000000 : ℝ)^3549
        have hw : |(5389638707/10000000000 : ℝ)|=(5389638707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614666461/5000000000 : ℝ)|^4573 ≤ (43371959406963/100000000000000 : ℝ)^3549
        have hw : |(2614666461/5000000000 : ℝ)|=(2614666461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870958053/10000000000 : ℝ)|^4573 ≤ (11535362566419/100000000000000 : ℝ)^3549
        have hw : |(-1870958053/10000000000 : ℝ)|=(1870958053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1538_box_15 (p : ℝ) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1003300719/2500000000 : ℝ)*x 0 + (4386343469/10000000000 : ℝ)*x 1 + (4386343587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003300719/2500000000 : ℝ)^4573 ≤ (30837958577081/100000000000000 : ℝ)^3549 := by
    have hnat : (1003300719 : ℕ)^4573*100000000000000^3549 ≤ 30837958577081^3549*2500000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003300719 2500000000 30837958577081 100000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4386343469/10000000000 : ℝ)^4573 ≤ (1729051004947/5000000000000 : ℝ)^3549 := by
    have hnat : (4386343469 : ℕ)^4573*5000000000000^3549 ≤ 1729051004947^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386343469 10000000000 1729051004947 5000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386343587/10000000000 : ℝ)^4573 ≤ (6916204259529/20000000000000 : ℝ)^3549 := by
    have hnat : (4386343587 : ℕ)^4573*20000000000000^3549 ≤ 6916204259529^3549*10000000000^4573 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386343587 10000000000 6916204259529 20000000000000 4573 3549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4573/1024 : ℝ)) 4573 3549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1003300719/2500000000 : ℝ), (4386343469/10000000000 : ℝ), (4386343587/10000000000 : ℝ)] ![(30837958577081/100000000000000 : ℝ), (1729051004947/5000000000000 : ℝ), (6916204259529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1003300719/2500000000 : ℝ)|^4573 ≤ (30837958577081/100000000000000 : ℝ)^3549
        have hw : |(1003300719/2500000000 : ℝ)|=(1003300719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4386343469/10000000000 : ℝ)|^4573 ≤ (1729051004947/5000000000000 : ℝ)^3549
        have hw : |(4386343469/10000000000 : ℝ)|=(4386343469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386343587/10000000000 : ℝ)|^4573 ≤ (6916204259529/20000000000000 : ℝ)^3549
        have hw : |(4386343587/10000000000 : ℝ)|=(4386343587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1538_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1993/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(47/80 : ℝ) ∧ (40297/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86167/100000 : ℝ) := by
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
  have lower0 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11013/100000 : ℝ) ^ (4571/1024 : ℝ) ≤ (528681386633123/10000000000000000000 : ℝ) := by
    have hpowers : (11013/100000 : ℝ)^4571 ≤ (528681386633123/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11013 : ℕ)^4571*10000000000000000000^1024 ≤ 528681386633123^1024*100000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11013 100000 528681386633123 10000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11013/100000 : ℝ)) (X := (528681386633123/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4571/1024 : ℝ) ≤ (6049034206184589/25000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4571 ≤ (6049034206184589/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4571*25000000000000000000^1024 ≤ 6049034206184589^1024*25000^4571 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 6049034206184589 25000000000000000000 4571 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (6049034206184589/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000528681386633123/5000000000000000000 : ℝ) ≤ (10000236861750971/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (5000528681386633123/5000000000000000000 : ℝ)^1024 ≤ (10000236861750971/10000000000000000 : ℝ)^4571 := by
      have hnat : (5000528681386633123 : ℕ)^1024*10000000000000000^4571 ≤ 10000236861750971^4571*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000528681386633123 5000000000000000000 10000236861750971 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000236861750971/10000000000000000 : ℝ)) (X := (5000528681386633123/5000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014741475345534793/50000000000000000000 : ℝ) ≤ (500033020223793/500000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (50014741475345534793/50000000000000000000 : ℝ)^1024 ≤ (500033020223793/500000000000000 : ℝ)^4571 := by
      have hnat : (50014741475345534793 : ℕ)^1024*500000000000000^4571 ≤ 500033020223793^4571*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014741475345534793 50000000000000000000 500033020223793 500000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500033020223793/500000000000000 : ℝ)) (X := (50014741475345534793/50000000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506049034206184589/12500000000000000000 : ℝ) ≤ (10001083947200749/10000000000000000 : ℝ) ^ (4571/1024 : ℝ) := by
    have hpowers : (12506049034206184589/12500000000000000000 : ℝ)^1024 ≤ (10001083947200749/10000000000000000 : ℝ)^4571 := by
      have hnat : (12506049034206184589 : ℕ)^1024*10000000000000000^4571 ≤ 10001083947200749^4571*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506049034206184589 12500000000000000000 10001083947200749 10000000000000000 1024 4571 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001083947200749/10000000000000000 : ℝ)) (X := (12506049034206184589/12500000000000000000 : ℝ)) (by norm_num) 4571 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(528681386633123/10000000000000000000 : ℝ) ≤ ((44701730056830186227/44710000000000000000 : ℝ)+2*(423542724889/447100000000000 : ℝ)*(11013/100000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (44701730056830186227/44710000000000000000 : ℝ)+2*(423542724889/447100000000000 : ℝ)*(11013/100000 : ℝ)=(10000236861750971/10000000000000000 : ℝ) by norm_num, show 1+2*(528681386633123/10000000000000000000 : ℝ)=(5000528681386633123/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6049034206184589/25000000000000000000 : ℝ)+(528681386633123/10000000000000000000 : ℝ) ≤ ((44701730056830186227/44710000000000000000 : ℝ)+(423542724889/447100000000000 : ℝ)*((3871/25000 : ℝ)+(11013/100000 : ℝ)))^(4571/1024 : ℝ) := by
    rw [show (44701730056830186227/44710000000000000000 : ℝ)+(423542724889/447100000000000 : ℝ)*((3871/25000 : ℝ)+(11013/100000 : ℝ))=(500033020223793/500000000000000 : ℝ) by norm_num, show 1+(6049034206184589/25000000000000000000 : ℝ)+(528681386633123/10000000000000000000 : ℝ)=(50014741475345534793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6049034206184589/25000000000000000000 : ℝ) ≤ ((44701730056830186227/44710000000000000000 : ℝ)+2*(423542724889/447100000000000 : ℝ)*(3871/25000 : ℝ))^(4571/1024 : ℝ) := by
    rw [show (44701730056830186227/44710000000000000000 : ℝ)+2*(423542724889/447100000000000 : ℝ)*(3871/25000 : ℝ)=(10001083947200749/10000000000000000 : ℝ) by norm_num, show 1+2*(6049034206184589/25000000000000000000 : ℝ)=(12506049034206184589/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44701730056830186227/44710000000000000000 : ℝ)*(X 1 0+X 2 0)+(423542724889/447100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44701730056830186227/44710000000000000000 : ℝ)) (alpha := (423542724889/447100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44701730056830186227/44710000000000000000 : ℝ)*(X 0 1+X 2 1)+(423542724889/447100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44701730056830186227/44710000000000000000 : ℝ)) (alpha := (423542724889/447100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44701730056830186227/44710000000000000000 : ℝ)*(X 0 2+X 1 2)+(423542724889/447100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4571/1024 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44701730056830186227/44710000000000000000 : ℝ)) (alpha := (423542724889/447100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1621193587/10000000000 : ℝ)*X 0 0+(5400025893/10000000000 : ℝ)*X 0 1+(1080005103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((65887927/125000000 : ℝ)*X 1 0+(-1800308213/10000000000 : ℝ)*X 1 1+(5400025973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271034593/10000000000 : ℝ)*X 2 0+(5400025599/10000000000 : ℝ)*X 2 1+(-225038517/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((222987423/500000000 : ℝ)*X 0 0+(4163669149/10000000000 : ℝ)*X 0 1+(130114667/312500000 : ℝ)*X 0 2+(222987423/500000000 : ℝ)*X 1 0+(4163669149/10000000000 : ℝ)*X 1 1+(130114667/312500000 : ℝ)*X 1 2+(222987423/500000000 : ℝ)*X 2 0+(4163669149/10000000000 : ℝ)*X 2 1+(130114667/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2044784771/10000000000 : ℝ)*X 0 0+(1311093739/2500000000 : ℝ)*X 0 1+(209775017/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2689593331/5000000000 : ℝ)*X 1 0+(-932445827/5000000000 : ℝ)*X 1 1+(2622187349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2689593223/5000000000 : ℝ)*X 2 0+(5244375447/10000000000 : ℝ)*X 2 1+(-932445469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4053340347/10000000000 : ℝ)*X 0 0+(2183371551/5000000000 : ℝ)*X 0 1+(4366741397/10000000000 : ℝ)*X 0 2+(4053340347/10000000000 : ℝ)*X 1 0+(2183371551/5000000000 : ℝ)*X 1 1+(4366741397/10000000000 : ℝ)*X 1 2+(4053340347/10000000000 : ℝ)*X 2 0+(2183371551/5000000000 : ℝ)*X 2 1+(4366741397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-391028149/2000000000 : ℝ)*X 0 0+(1027010297/2000000000 : ℝ)*X 0 1+(5420398433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256874001/10000000000 : ℝ)*X 1 0+(-1791615489/10000000000 : ℝ)*X 1 1+(5420398329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628436777/5000000000 : ℝ)*X 2 0+(5420398837/10000000000 : ℝ)*X 2 1+(-895807699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140993581/312500000 : ℝ)*X 0 0+(129283013/312500000 : ℝ)*X 0 1+(827411153/2000000000 : ℝ)*X 0 2+(140993581/312500000 : ℝ)*X 1 0+(129283013/312500000 : ℝ)*X 1 1+(827411153/2000000000 : ℝ)*X 1 2+(140993581/312500000 : ℝ)*X 2 0+(129283013/312500000 : ℝ)*X 2 1+(827411153/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1710652059/10000000000 : ℝ)*X 0 0+(2752960131/5000000000 : ℝ)*X 0 1+(5229333057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389638927/10000000000 : ℝ)*X 1 0+(-374191573/2000000000 : ℝ)*X 1 1+(130733321/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5389638707/10000000000 : ℝ)*X 2 0+(2614666461/5000000000 : ℝ)*X 2 1+(-1870958053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1003300719/2500000000 : ℝ)*X 0 0+(4386343469/10000000000 : ℝ)*X 0 1+(4386343587/10000000000 : ℝ)*X 0 2+(1003300719/2500000000 : ℝ)*X 1 0+(4386343469/10000000000 : ℝ)*X 1 1+(4386343587/10000000000 : ℝ)*X 1 2+(1003300719/2500000000 : ℝ)*X 2 0+(4386343469/10000000000 : ℝ)*X 2 1+(4386343587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1538_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1993/3125 : ℝ) ≤ (-712828536601051730815311947431167/1117750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17809451/25000000000000 : ℝ)*(lower0) + (75275529/100000000000000 : ℝ)*(upper1) + (84931661/50000000000000 : ℝ)*(lower2) + (1130793557691593/50000000000000 : ℝ)*(major0) + (1130793557691593/50000000000000 : ℝ)*(major1) + (1130793557691593/50000000000000 : ℝ)*(major2) + (14076583017/100000000000000 : ℝ)*(sp1) + (503866579/20000000000000 : ℝ)*(sp3) + (3177576494972271/100000000000000 : ℝ)*(sp4) + (3177566018445057/100000000000000 : ℝ)*(sp5) + (1588748785013589/50000000000000 : ℝ)*(sp6) + (1366849456906437/100000000000000 : ℝ)*(sp7) + (3600055803/100000000000000 : ℝ)*(sp8) + (1289453139/1562500000000 : ℝ)*(sp14) + (341712994059833/25000000000000 : ℝ)*(f.failure) + (1588790047514037/50000000000000 : ℝ)*(f.sum) + (131200765912511/22355000000000000000000000000 : ℝ)*base66 + (4884813292909989611/2235500000000000000000000000000000 : ℝ)*base67 + (1561415898986510389/2235500000000000000000000000000000 : ℝ)*base70 + (5339087981011510389/2235500000000000000000000000000000 : ℝ)*base72 + (538066947511/349296875000000000000000000 : ℝ)*base73 + (9926816632168010389/2235500000000000000000000000000000 : ℝ)*base76 + (7045714298624510389/2235500000000000000000000000000000 : ℝ)*base78 + (18893944807291489611/2235500000000000000000000000000000 : ℝ)*base79 + (93286412153181/22355000000000000000000000000 : ℝ)*base82 + (2804683/2500000000000000000000 : ℝ)*base90 + (2804683/2500000000000000000000 : ℝ)*base92 + (2804683/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (47/80 : ℝ) ≤ (1313421905386440529443895418512167/2235500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92261529/100000000000000 : ℝ)*(lower1) + (111420471/100000000000000 : ℝ)*(upper4) + (11155441/50000000000000 : ℝ)*(lower5) + (1169808856334901/50000000000000 : ℝ)*(major0) + (1169808856334901/50000000000000 : ℝ)*(major1) + (2339617712669803/100000000000000 : ℝ)*(major2) + (129825445724767/4000000000000 : ℝ)*(sp0) + (1622817995996651/50000000000000 : ℝ)*(sp1) + (405704835510939/12500000000000 : ℝ)*(sp2) + (707004602129669/50000000000000 : ℝ)*(sp3) + (3220956957/100000000000000 : ℝ)*(sp5) + (264431373/50000000000000 : ℝ)*(sp6) + (539163057/20000000000000 : ℝ)*(sp7) + (3069831083/100000000000000 : ℝ)*(sp8) + (11046967969333/781250000000 : ℝ)*(f.failure) + (1622819606475129/50000000000000 : ℝ)*(f.sum) + (43379727968039/8942000000000000000000000000 : ℝ)*base65 + (14282463893198041473/2235500000000000000000000000000000 : ℝ)*base68 + (1012700188503796719/4471000000000000000000000000000000 : ℝ)*base70 + (15888767366576541473/2235500000000000000000000000000000 : ℝ)*base72 + (1145451104993/8942000000000000000000000000 : ℝ)*base73 + (5154025495231796719/4471000000000000000000000000000000 : ℝ)*base76 + (7337113805889991473/2235500000000000000000000000000000 : ℝ)*base78 + (10879996520452491473/2235500000000000000000000000000000 : ℝ)*base80 + (108863975404843/22355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1198317/78125000000000000000 : ℝ)*base89 + (1198317/78125000000000000000 : ℝ)*base91 + (417067/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40297/50000 : ℝ) ≤ (180173795501774803489886949107949/223550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26771991/100000000000000 : ℝ)*(upper1) + (1036303/20000000000000 : ℝ)*(upper3) + (7482257/100000000000000 : ℝ)*(upper4) + (136460379/100000000000000 : ℝ)*(lower5) + (253032327406743/10000000000000 : ℝ)*(major0) + (253032327406743/10000000000000 : ℝ)*(major1) + (253032327406743/10000000000000 : ℝ)*(major2) + (364612431/5000000000000 : ℝ)*(sp0) + (115905265807/100000000000000 : ℝ)*(sp2) + (46733672031/100000000000000 : ℝ)*(sp3) + (3504503690635989/100000000000000 : ℝ)*(sp8) + (350451098288461/10000000000000 : ℝ)*(sp9) + (1752197538809401/50000000000000 : ℝ)*(sp10) + (1529223283900319/100000000000000 : ℝ)*(sp11) + (30585400351447/2000000000000 : ℝ)*(f.failure) + (350451098288461/10000000000000 : ℝ)*(f.sum) + (16506554955081/4471000000000000000000000000 : ℝ)*base65 + (2939483977302571339/447100000000000000000000000000000 : ℝ)*base68 + (3340519974297371339/447100000000000000000000000000000 : ℝ)*base70 + (2178315036799571339/447100000000000000000000000000000 : ℝ)*base72 + (6273246681511/4471000000000000000000000000 : ℝ)*base73 + (6189115753903671339/447100000000000000000000000000000 : ℝ)*base76 + (4320817901027471339/447100000000000000000000000000000 : ℝ)*base78 + (4587993246710771339/447100000000000000000000000000000 : ℝ)*base80 + (15213262818333/4471000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2117403/200000000000000000000 : ℝ)*base89 + (2117403/200000000000000000000 : ℝ)*base91 + (2117403/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-86167/100000 : ℝ) ≤ (-1926212224493998924317005022468267/2235500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51600909/100000000000000 : ℝ)*(upper3) + (83146661/100000000000000 : ℝ)*(lower4) + (4053493/100000000000000 : ℝ)*(upper5) + (2570021648342493/100000000000000 : ℝ)*(major0) + (2570021648342493/100000000000000 : ℝ)*(major1) + (2570021648342493/100000000000000 : ℝ)*(major2) + (1416948533/50000000000000 : ℝ)*(sp4) + (22324395539/25000000000000 : ℝ)*(sp5) + (11593402507/12500000000000 : ℝ)*(sp6) + (240734397/800000000000 : ℝ)*(sp7) + (1807749609924061/50000000000000 : ℝ)*(sp12) + (451926594520379/12500000000000 : ℝ)*(sp13) + (903852326631283/25000000000000 : ℝ)*(sp14) + (155323272311503/10000000000000 : ℝ)*(sp15) + (310652562982931/20000000000000 : ℝ)*(f.failure) + (903875513436297/25000000000000 : ℝ)*(f.sum) + (3908939227009/2794375000000000000000000000 : ℝ)*base65 + (2559905947415143911/4471000000000000000000000000000000 : ℝ)*base67 + (33262451840173856089/4471000000000000000000000000000000 : ℝ)*base70 + (22238241648965856089/4471000000000000000000000000000000 : ℝ)*base72 + (16634626249903/22355000000000000000000000000 : ℝ)*base74 + (1028831566982143911/4471000000000000000000000000000000 : ℝ)*base75 + (20807948021409856089/4471000000000000000000000000000000 : ℝ)*base78 + (11235962217980856089/4471000000000000000000000000000000 : ℝ)*base80 + (24093979837157/5588750000000000000000000000 : ℝ)*base82 + (2041881/2000000000000000000000 : ℝ)*base90 + (2041881/2000000000000000000000 : ℝ)*base92 + (2041881/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1538_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1993/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(47/80 : ℝ) else (40297/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86167/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1538_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1538_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1993/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(47/80 : ℝ) else (40297/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86167/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1538_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1538_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4571/1024 : ℝ) ≤ p) (hpb : p ≤ (4573/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165459549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1993/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(47/80 : ℝ) else (40297/50000 : ℝ) ≤ X j i ∧ X j i ≤ (86167/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1538_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
