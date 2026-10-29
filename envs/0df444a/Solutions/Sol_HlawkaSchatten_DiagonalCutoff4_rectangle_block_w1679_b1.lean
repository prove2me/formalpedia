-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1679_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:01.487183+00:00
-- url     : https://prove2.me/submissions/50fd018d-66cd-466d-af72-f757f9882c31

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
theorem support_rectangle_w1679_s3_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-766237379/5000000000 : ℝ)*x 0 + (5490813967/10000000000 : ℝ)*x 1 + (160410851/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766237379/5000000000 : ℝ)^5055 ≤ (9516073172221/100000000000000 : ℝ)^4031 := by
    have hnat : (766237379 : ℕ)^5055*100000000000000^4031 ≤ 9516073172221^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766237379 5000000000 9516073172221 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490813967/10000000000 : ℝ)^5055 ≤ (47151587669197/100000000000000 : ℝ)^4031 := by
    have hnat : (5490813967 : ℕ)^5055*100000000000000^4031 ≤ 47151587669197^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490813967 10000000000 47151587669197 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160410851/312500000 : ℝ)^5055 ≤ (8666467829189/20000000000000 : ℝ)^4031 := by
    have hnat : (160410851 : ℕ)^5055*20000000000000^4031 ≤ 8666467829189^4031*312500000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160410851 312500000 8666467829189 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-766237379/5000000000 : ℝ), (5490813967/10000000000 : ℝ), (160410851/312500000 : ℝ)] ![(9516073172221/100000000000000 : ℝ), (47151587669197/100000000000000 : ℝ), (8666467829189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-766237379/5000000000 : ℝ)|^5055 ≤ (9516073172221/100000000000000 : ℝ)^4031
        have hw : |(-766237379/5000000000 : ℝ)|=(766237379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490813967/10000000000 : ℝ)|^5055 ≤ (47151587669197/100000000000000 : ℝ)^4031
        have hw : |(5490813967/10000000000 : ℝ)|=(5490813967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160410851/312500000 : ℝ)|^5055 ≤ (8666467829189/20000000000000 : ℝ)^4031
        have hw : |(160410851/312500000 : ℝ)|=(160410851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070775183/2000000000 : ℝ)*x 0 + (-429615097/2500000000 : ℝ)*x 1 + (5133146879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070775183/2000000000 : ℝ)^5055 ≤ (2855101723311/6250000000000 : ℝ)^4031 := by
    have hnat : (1070775183 : ℕ)^5055*6250000000000^4031 ≤ 2855101723311^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070775183 2000000000 2855101723311 6250000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429615097/2500000000 : ℝ)^5055 ≤ (1373254625273/12500000000000 : ℝ)^4031 := by
    have hnat : (429615097 : ℕ)^5055*12500000000000^4031 ≤ 1373254625273^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429615097 2500000000 1373254625273 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133146879/10000000000 : ℝ)^5055 ≤ (8666467081809/20000000000000 : ℝ)^4031 := by
    have hnat : (5133146879 : ℕ)^5055*20000000000000^4031 ≤ 8666467081809^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133146879 10000000000 8666467081809 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070775183/2000000000 : ℝ), (-429615097/2500000000 : ℝ), (5133146879/10000000000 : ℝ)] ![(2855101723311/6250000000000 : ℝ), (1373254625273/12500000000000 : ℝ), (8666467081809/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070775183/2000000000 : ℝ)|^5055 ≤ (2855101723311/6250000000000 : ℝ)^4031
        have hw : |(1070775183/2000000000 : ℝ)|=(1070775183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429615097/2500000000 : ℝ)|^5055 ≤ (1373254625273/12500000000000 : ℝ)^4031
        have hw : |(-429615097/2500000000 : ℝ)|=(429615097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133146879/10000000000 : ℝ)|^5055 ≤ (8666467081809/20000000000000 : ℝ)^4031
        have hw : |(5133146879/10000000000 : ℝ)|=(5133146879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070775301/2000000000 : ℝ)*x 0 + (5133146307/10000000000 : ℝ)*x 1 + (-343692071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070775301/2000000000 : ℝ)^5055 ≤ (9136326777189/20000000000000 : ℝ)^4031 := by
    have hnat : (1070775301 : ℕ)^5055*20000000000000^4031 ≤ 9136326777189^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070775301 2000000000 9136326777189 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133146307/10000000000 : ℝ)^5055 ≤ (8666465870757/20000000000000 : ℝ)^4031 := by
    have hnat : (5133146307 : ℕ)^5055*20000000000000^4031 ≤ 8666465870757^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133146307 10000000000 8666465870757 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343692071/2000000000 : ℝ)^5055 ≤ (1373254592203/12500000000000 : ℝ)^4031 := by
    have hnat : (343692071 : ℕ)^5055*12500000000000^4031 ≤ 1373254592203^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343692071 2000000000 1373254592203 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070775301/2000000000 : ℝ), (5133146307/10000000000 : ℝ), (-343692071/2000000000 : ℝ)] ![(9136326777189/20000000000000 : ℝ), (8666465870757/20000000000000 : ℝ), (1373254592203/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070775301/2000000000 : ℝ)|^5055 ≤ (9136326777189/20000000000000 : ℝ)^4031
        have hw : |(1070775301/2000000000 : ℝ)|=(1070775301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133146307/10000000000 : ℝ)|^5055 ≤ (8666465870757/20000000000000 : ℝ)^4031
        have hw : |(5133146307/10000000000 : ℝ)|=(5133146307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343692071/2000000000 : ℝ)|^5055 ≤ (1373254592203/12500000000000 : ℝ)^4031
        have hw : |(-343692071/2000000000 : ℝ)|=(343692071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2073301947/5000000000 : ℝ)*x 0 + (147356023/400000000 : ℝ)*x 1 + (1161963309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073301947/5000000000 : ℝ)^5055 ≤ (33156945017859/100000000000000 : ℝ)^4031 := by
    have hnat : (2073301947 : ℕ)^5055*100000000000000^4031 ≤ 33156945017859^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073301947 5000000000 33156945017859 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147356023/400000000 : ℝ)^5055 ≤ (571697833779/2000000000000 : ℝ)^4031 := by
    have hnat : (147356023 : ℕ)^5055*2000000000000^4031 ≤ 571697833779^4031*400000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147356023 400000000 571697833779 2000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161963309/2500000000 : ℝ)^5055 ≤ (1530326530673/4000000000000 : ℝ)^4031 := by
    have hnat : (1161963309 : ℕ)^5055*4000000000000^4031 ≤ 1530326530673^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161963309 2500000000 1530326530673 4000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073301947/5000000000 : ℝ), (147356023/400000000 : ℝ), (1161963309/2500000000 : ℝ)] ![(33156945017859/100000000000000 : ℝ), (571697833779/2000000000000 : ℝ), (1530326530673/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073301947/5000000000 : ℝ)|^5055 ≤ (33156945017859/100000000000000 : ℝ)^4031
        have hw : |(2073301947/5000000000 : ℝ)|=(2073301947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147356023/400000000 : ℝ)|^5055 ≤ (571697833779/2000000000000 : ℝ)^4031
        have hw : |(147356023/400000000 : ℝ)|=(147356023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161963309/2500000000 : ℝ)|^5055 ≤ (1530326530673/4000000000000 : ℝ)^4031
        have hw : |(1161963309/2500000000 : ℝ)|=(1161963309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-766321893/5000000000 : ℝ)*x 0 + (5137002333/10000000000 : ℝ)*x 1 + (2743450663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766321893/5000000000 : ℝ)^5055 ≤ (9517389419667/100000000000000 : ℝ)^4031 := by
    have hnat : (766321893 : ℕ)^5055*100000000000000^4031 ≤ 9517389419667^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766321893 5000000000 9517389419667 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137002333/10000000000 : ℝ)^5055 ≤ (5421644199547/12500000000000 : ℝ)^4031 := by
    have hnat : (5137002333 : ℕ)^5055*12500000000000^4031 ≤ 5421644199547^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137002333 10000000000 5421644199547 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743450663/5000000000 : ℝ)^5055 ≤ (23554728486387/50000000000000 : ℝ)^4031 := by
    have hnat : (2743450663 : ℕ)^5055*50000000000000^4031 ≤ 23554728486387^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743450663 5000000000 23554728486387 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-766321893/5000000000 : ℝ), (5137002333/10000000000 : ℝ), (2743450663/5000000000 : ℝ)] ![(9517389419667/100000000000000 : ℝ), (5421644199547/12500000000000 : ℝ), (23554728486387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-766321893/5000000000 : ℝ)|^5055 ≤ (9517389419667/100000000000000 : ℝ)^4031
        have hw : |(-766321893/5000000000 : ℝ)|=(766321893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137002333/10000000000 : ℝ)|^5055 ≤ (5421644199547/12500000000000 : ℝ)^4031
        have hw : |(5137002333/10000000000 : ℝ)|=(5137002333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743450663/5000000000 : ℝ)|^5055 ≤ (23554728486387/50000000000000 : ℝ)^4031
        have hw : |(2743450663/5000000000 : ℝ)|=(2743450663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629192827/5000000000 : ℝ)*x 0 + (-1364705501/10000000000 : ℝ)*x 1 + (2743450633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629192827/5000000000 : ℝ)^5055 ≤ (34892353007/78125000000 : ℝ)^4031 := by
    have hnat : (2629192827 : ℕ)^5055*78125000000^4031 ≤ 34892353007^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629192827 5000000000 34892353007 78125000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364705501/10000000000 : ℝ)^5055 ≤ (8228331815459/100000000000000 : ℝ)^4031 := by
    have hnat : (1364705501 : ℕ)^5055*100000000000000^4031 ≤ 8228331815459^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364705501 10000000000 8228331815459 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743450633/5000000000 : ℝ)^5055 ≤ (23554728163381/50000000000000 : ℝ)^4031 := by
    have hnat : (2743450633 : ℕ)^5055*50000000000000^4031 ≤ 23554728163381^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743450633 5000000000 23554728163381 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629192827/5000000000 : ℝ), (-1364705501/10000000000 : ℝ), (2743450633/5000000000 : ℝ)] ![(34892353007/78125000000 : ℝ), (8228331815459/100000000000000 : ℝ), (23554728163381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629192827/5000000000 : ℝ)|^5055 ≤ (34892353007/78125000000 : ℝ)^4031
        have hw : |(2629192827/5000000000 : ℝ)|=(2629192827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364705501/10000000000 : ℝ)|^5055 ≤ (8228331815459/100000000000000 : ℝ)^4031
        have hw : |(-1364705501/10000000000 : ℝ)|=(1364705501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743450633/5000000000 : ℝ)|^5055 ≤ (23554728163381/50000000000000 : ℝ)^4031
        have hw : |(2743450633/5000000000 : ℝ)|=(2743450633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258385751/10000000000 : ℝ)*x 0 + (5486901209/10000000000 : ℝ)*x 1 + (-682352723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258385751/10000000000 : ℝ)^5055 ≤ (1116555322053/2500000000000 : ℝ)^4031 := by
    have hnat : (5258385751 : ℕ)^5055*2500000000000^4031 ≤ 1116555322053^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258385751 10000000000 1116555322053 2500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486901209/10000000000 : ℝ)^5055 ≤ (47109455713051/100000000000000 : ℝ)^4031 := by
    have hnat : (5486901209 : ℕ)^5055*100000000000000^4031 ≤ 47109455713051^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486901209 10000000000 47109455713051 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682352723/5000000000 : ℝ)^5055 ≤ (4114165699801/50000000000000 : ℝ)^4031 := by
    have hnat : (682352723 : ℕ)^5055*50000000000000^4031 ≤ 4114165699801^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682352723 5000000000 4114165699801 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258385751/10000000000 : ℝ), (5486901209/10000000000 : ℝ), (-682352723/5000000000 : ℝ)] ![(1116555322053/2500000000000 : ℝ), (47109455713051/100000000000000 : ℝ), (4114165699801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258385751/10000000000 : ℝ)|^5055 ≤ (1116555322053/2500000000000 : ℝ)^4031
        have hw : |(5258385751/10000000000 : ℝ)|=(5258385751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486901209/10000000000 : ℝ)|^5055 ≤ (47109455713051/100000000000000 : ℝ)^4031
        have hw : |(5486901209/10000000000 : ℝ)|=(5486901209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682352723/5000000000 : ℝ)|^5055 ≤ (4114165699801/50000000000000 : ℝ)^4031
        have hw : |(-682352723/5000000000 : ℝ)|=(682352723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s3_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4147059219/10000000000 : ℝ)*x 0 + (4637461661/10000000000 : ℝ)*x 1 + (3694448011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147059219/10000000000 : ℝ)^5055 ≤ (16580755414129/50000000000000 : ℝ)^4031 := by
    have hnat : (4147059219 : ℕ)^5055*50000000000000^4031 ≤ 16580755414129^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147059219 10000000000 16580755414129 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4637461661/10000000000 : ℝ)^5055 ≤ (3815092790247/10000000000000 : ℝ)^4031 := by
    have hnat : (4637461661 : ℕ)^5055*10000000000000^4031 ≤ 3815092790247^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637461661 10000000000 3815092790247 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3694448011/10000000000 : ℝ)^5055 ≤ (7171890312537/25000000000000 : ℝ)^4031 := by
    have hnat : (3694448011 : ℕ)^5055*25000000000000^4031 ≤ 7171890312537^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694448011 10000000000 7171890312537 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147059219/10000000000 : ℝ), (4637461661/10000000000 : ℝ), (3694448011/10000000000 : ℝ)] ![(16580755414129/50000000000000 : ℝ), (3815092790247/10000000000000 : ℝ), (7171890312537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147059219/10000000000 : ℝ)|^5055 ≤ (16580755414129/50000000000000 : ℝ)^4031
        have hw : |(4147059219/10000000000 : ℝ)|=(4147059219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4637461661/10000000000 : ℝ)|^5055 ≤ (3815092790247/10000000000000 : ℝ)^4031
        have hw : |(4637461661/10000000000 : ℝ)|=(4637461661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3694448011/10000000000 : ℝ)|^5055 ≤ (7171890312537/25000000000000 : ℝ)^4031
        have hw : |(3694448011/10000000000 : ℝ)|=(3694448011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9713/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17313/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8673/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1937/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8673/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1937/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8673/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1937/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8673/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1937/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8673/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1937/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8673/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1937/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1937/20000 : ℝ) ^ (5047/1024 : ℝ) ≤ (503208695097709/50000000000000000000 : ℝ) := by
    have hpowers : (1937/20000 : ℝ)^5047 ≤ (503208695097709/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1937 : ℕ)^5047*50000000000000000000^1024 ≤ 503208695097709^1024*20000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1937 20000 503208695097709 50000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1937/20000 : ℝ)) (X := (503208695097709/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8673/50000 : ℝ) ^ (5047/1024 : ℝ) ≤ (711694266737049/4000000000000000000 : ℝ) := by
    have hpowers : (8673/50000 : ℝ)^5047 ≤ (711694266737049/4000000000000000000 : ℝ)^1024 := by
      have hnat : (8673 : ℕ)^5047*4000000000000000000^1024 ≤ 711694266737049^1024*50000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8673 50000 711694266737049 4000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8673/50000 : ℝ)) (X := (711694266737049/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000503208695097709/25000000000000000000 : ℝ) ≤ (1000004083864237/1000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (25000503208695097709/25000000000000000000 : ℝ)^1024 ≤ (1000004083864237/1000000000000000 : ℝ)^5047 := by
      have hnat : (25000503208695097709 : ℕ)^1024*1000000000000000^5047 ≤ 1000004083864237^5047*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000503208695097709 25000000000000000000 1000004083864237 1000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000004083864237/1000000000000000 : ℝ)) (X := (25000503208695097709/25000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018798774058621643/100000000000000000000 : ℝ) ≤ (10000381385031329/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (100018798774058621643/100000000000000000000 : ℝ)^1024 ≤ (10000381385031329/10000000000000000 : ℝ)^5047 := by
      have hnat : (100018798774058621643 : ℕ)^1024*10000000000000000^5047 ≤ 10000381385031329^5047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018798774058621643 100000000000000000000 10000381385031329 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000381385031329/10000000000000000 : ℝ)) (X := (100018798774058621643/100000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000711694266737049/2000000000000000000 : ℝ) ≤ (78130640089221/78125000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (2000711694266737049/2000000000000000000 : ℝ)^1024 ≤ (78130640089221/78125000000000 : ℝ)^5047 := by
      have hnat : (2000711694266737049 : ℕ)^1024*78125000000000^5047 ≤ 78130640089221^5047*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000711694266737049 2000000000000000000 78130640089221 78125000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78130640089221/78125000000000 : ℝ)) (X := (2000711694266737049/2000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(503208695097709/50000000000000000000 : ℝ) ≤ ((3830185824064253037/3830500000000000000 : ℝ)+2*(340546388959/766100000000000 : ℝ)*(1937/20000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (3830185824064253037/3830500000000000000 : ℝ)+2*(340546388959/766100000000000 : ℝ)*(1937/20000 : ℝ)=(1000004083864237/1000000000000000 : ℝ) by norm_num, show 1+2*(503208695097709/50000000000000000000 : ℝ)=(25000503208695097709/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(711694266737049/4000000000000000000 : ℝ)+(503208695097709/50000000000000000000 : ℝ) ≤ ((3830185824064253037/3830500000000000000 : ℝ)+(340546388959/766100000000000 : ℝ)*((8673/50000 : ℝ)+(1937/20000 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (3830185824064253037/3830500000000000000 : ℝ)+(340546388959/766100000000000 : ℝ)*((8673/50000 : ℝ)+(1937/20000 : ℝ))=(10000381385031329/10000000000000000 : ℝ) by norm_num, show 1+(711694266737049/4000000000000000000 : ℝ)+(503208695097709/50000000000000000000 : ℝ)=(100018798774058621643/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(711694266737049/4000000000000000000 : ℝ) ≤ ((3830185824064253037/3830500000000000000 : ℝ)+2*(340546388959/766100000000000 : ℝ)*(8673/50000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (3830185824064253037/3830500000000000000 : ℝ)+2*(340546388959/766100000000000 : ℝ)*(8673/50000 : ℝ)=(78130640089221/78125000000000 : ℝ) by norm_num, show 1+2*(711694266737049/4000000000000000000 : ℝ)=(2000711694266737049/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3830185824064253037/3830500000000000000 : ℝ)*(X 1 0+X 2 0)+(340546388959/766100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1937/20000 : ℝ)) (hi := (8673/50000 : ℝ)) (c := (3830185824064253037/3830500000000000000 : ℝ)) (alpha := (340546388959/766100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3830185824064253037/3830500000000000000 : ℝ)*(X 0 1+X 2 1)+(340546388959/766100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1937/20000 : ℝ)) (hi := (8673/50000 : ℝ)) (c := (3830185824064253037/3830500000000000000 : ℝ)) (alpha := (340546388959/766100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3830185824064253037/3830500000000000000 : ℝ)*(X 0 2+X 1 2)+(340546388959/766100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1937/20000 : ℝ)) (hi := (8673/50000 : ℝ)) (c := (3830185824064253037/3830500000000000000 : ℝ)) (alpha := (340546388959/766100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-766237379/5000000000 : ℝ)*X 0 0+(5490813967/10000000000 : ℝ)*X 0 1+(160410851/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070775183/2000000000 : ℝ)*X 1 0+(-429615097/2500000000 : ℝ)*X 1 1+(5133146879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070775301/2000000000 : ℝ)*X 2 0+(5133146307/10000000000 : ℝ)*X 2 1+(-343692071/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2073301947/5000000000 : ℝ)*X 0 0+(147356023/400000000 : ℝ)*X 0 1+(1161963309/2500000000 : ℝ)*X 0 2+(2073301947/5000000000 : ℝ)*X 1 0+(147356023/400000000 : ℝ)*X 1 1+(1161963309/2500000000 : ℝ)*X 1 2+(2073301947/5000000000 : ℝ)*X 2 0+(147356023/400000000 : ℝ)*X 2 1+(1161963309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-766321893/5000000000 : ℝ)*X 0 0+(5137002333/10000000000 : ℝ)*X 0 1+(2743450663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629192827/5000000000 : ℝ)*X 1 0+(-1364705501/10000000000 : ℝ)*X 1 1+(2743450633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258385751/10000000000 : ℝ)*X 2 0+(5486901209/10000000000 : ℝ)*X 2 1+(-682352723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4147059219/10000000000 : ℝ)*X 0 0+(4637461661/10000000000 : ℝ)*X 0 1+(3694448011/10000000000 : ℝ)*X 0 2+(4147059219/10000000000 : ℝ)*X 1 0+(4637461661/10000000000 : ℝ)*X 1 1+(3694448011/10000000000 : ℝ)*X 1 2+(4147059219/10000000000 : ℝ)*X 2 0+(4637461661/10000000000 : ℝ)*X 2 1+(3694448011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297964067211499353569076873/23940625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (437919781/25000000000000 : ℝ)*(base19) + (1907895457/100000000000000 : ℝ)*(base23) + (4066147/5000000000000 : ℝ)*(lower2) + (1325853/390625000000 : ℝ)*(upper3) + (291083673/100000000000000 : ℝ)*(upper5) + (119791536501497/6250000000000 : ℝ)*(major0) + (119791536501497/6250000000000 : ℝ)*(major1) + (119791536501497/6250000000000 : ℝ)*(major2) + (279590927913429/10000000000000 : ℝ)*(sp0) + (1397959620933599/50000000000000 : ℝ)*(sp1) + (1397959542825433/50000000000000 : ℝ)*(sp2) + (259350259949219/25000000000000 : ℝ)*(sp3) + (11714412033/100000000000000 : ℝ)*(sp4) + (1679959837/25000000000000 : ℝ)*(sp7) + (4052374061079/390625000000 : ℝ)*(f.failure) + (1397960496773161/50000000000000 : ℝ)*(f.sum) + (43290990832289/19152500000000000000000000000 : ℝ)*base65 + (32042180028694757/11970312500000000000000000000000 : ℝ)*base67 + (353561793895655139/23940625000000000000000000000000 : ℝ)*base69 + (308212218927642639/23940625000000000000000000000000 : ℝ)*base71 + (4439313051047/2394062500000000000000000000 : ℝ)*base74 + (346419491381142639/23940625000000000000000000000000 : ℝ)*base75 + (233767237637767639/23940625000000000000000000000000 : ℝ)*base77 + (182486301482942639/23940625000000000000000000000000 : ℝ)*base79 + (100933225581549/19152500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (549701/39062500000000000000 : ℝ)*base90 + (549701/39062500000000000000 : ℝ)*base92 + (549701/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118300091633615809571634537/47881250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43076753/12500000000000 : ℝ)*(base19) + (206809477/50000000000000 : ℝ)*(base23) + (49203207/50000000000000 : ℝ)*(lower1) + (312293/781250000000 : ℝ)*(upper3) + (7006763/100000000000000 : ℝ)*(lower4) + (2943227/4000000000000 : ℝ)*(upper5) + (979598613896833/50000000000000 : ℝ)*(major0) + (979598613896833/50000000000000 : ℝ)*(major1) + (979598613896833/50000000000000 : ℝ)*(major2) + (81496241/50000000000000 : ℝ)*(sp2) + (571593106096721/20000000000000 : ℝ)*(sp4) + (2857965185869581/100000000000000 : ℝ)*(sp5) + (2857964953872169/100000000000000 : ℝ)*(sp6) + (106042884274713/10000000000000 : ℝ)*(sp7) + (106042884274713/10000000000000 : ℝ)*(f.failure) + (571593106096721/20000000000000 : ℝ)*(f.sum) + (21416639441503/19152500000000000000000000000 : ℝ)*base66 + (4426141099281791821/191525000000000000000000000000000 : ℝ)*base67 + (930218943902666821/191525000000000000000000000000000 : ℝ)*base69 + (1740781769827933179/191525000000000000000000000000000 : ℝ)*base72 + (238350131327749/38305000000000000000000000000 : ℝ)*base73 + (239957229155766821/191525000000000000000000000000000 : ℝ)*base75 + (677966702480691821/191525000000000000000000000000000 : ℝ)*base77 + (813718008691041821/191525000000000000000000000000000 : ℝ)*base79 + (47437597681791/9576250000000000000000000000 : ℝ)*base81 + (5961947/1000000000000000000000 : ℝ)*base90 + (5961947/1000000000000000000000 : ℝ)*base92 + (5961947/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1679_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9713/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1679_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1679_s4_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1532497137/10000000000 : ℝ)*x 0 + (1372681999/2500000000 : ℝ)*x 1 + (320826139/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1532497137/10000000000 : ℝ)^5055 ≤ (1189530929859/12500000000000 : ℝ)^4031 := by
    have hnat : (1532497137 : ℕ)^5055*12500000000000^4031 ≤ 1189530929859^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532497137 10000000000 1189530929859 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372681999/2500000000 : ℝ)^5055 ≤ (9430132373033/20000000000000 : ℝ)^4031 := by
    have hnat : (1372681999 : ℕ)^5055*20000000000000^4031 ≤ 9430132373033^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372681999 2500000000 9430132373033 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320826139/625000000 : ℝ)^5055 ≤ (4333309067703/10000000000000 : ℝ)^4031 := by
    have hnat : (320826139 : ℕ)^5055*10000000000000^4031 ≤ 4333309067703^4031*625000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320826139 625000000 4333309067703 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1532497137/10000000000 : ℝ), (1372681999/2500000000 : ℝ), (320826139/625000000 : ℝ)] ![(1189530929859/12500000000000 : ℝ), (9430132373033/20000000000000 : ℝ), (4333309067703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1532497137/10000000000 : ℝ)|^5055 ≤ (1189530929859/12500000000000 : ℝ)^4031
        have hw : |(-1532497137/10000000000 : ℝ)|=(1532497137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372681999/2500000000 : ℝ)|^5055 ≤ (9430132373033/20000000000000 : ℝ)^4031
        have hw : |(1372681999/2500000000 : ℝ)|=(1372681999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320826139/625000000 : ℝ)|^5055 ≤ (4333309067703/10000000000000 : ℝ)^4031
        have hw : |(320826139/625000000 : ℝ)|=(320826139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669231649/1250000000 : ℝ)*x 0 + (-859199781/5000000000 : ℝ)*x 1 + (513321591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669231649/1250000000 : ℝ)^5055 ≤ (4568138443821/10000000000000 : ℝ)^4031 := by
    have hnat : (669231649 : ℕ)^5055*10000000000000^4031 ≤ 4568138443821^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669231649 1250000000 4568138443821 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859199781/5000000000 : ℝ)^5055 ≤ (10985549364569/100000000000000 : ℝ)^4031 := by
    have hnat : (859199781 : ℕ)^5055*100000000000000^4031 ≤ 10985549364569^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859199781 5000000000 10985549364569 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513321591/1000000000 : ℝ)^5055 ≤ (21666533090333/50000000000000 : ℝ)^4031 := by
    have hnat : (513321591 : ℕ)^5055*50000000000000^4031 ≤ 21666533090333^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513321591 1000000000 21666533090333 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669231649/1250000000 : ℝ), (-859199781/5000000000 : ℝ), (513321591/1000000000 : ℝ)] ![(4568138443821/10000000000000 : ℝ), (10985549364569/100000000000000 : ℝ), (21666533090333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669231649/1250000000 : ℝ)|^5055 ≤ (4568138443821/10000000000000 : ℝ)^4031
        have hw : |(669231649/1250000000 : ℝ)|=(669231649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859199781/5000000000 : ℝ)|^5055 ≤ (10985549364569/100000000000000 : ℝ)^4031
        have hw : |(-859199781/5000000000 : ℝ)|=(859199781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513321591/1000000000 : ℝ)|^5055 ≤ (21666533090333/50000000000000 : ℝ)^4031
        have hw : |(513321591/1000000000 : ℝ)|=(513321591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353852877/10000000000 : ℝ)*x 0 + (2566608383/5000000000 : ℝ)*x 1 + (-429599713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353852877/10000000000 : ℝ)^5055 ≤ (4568138106773/10000000000000 : ℝ)^4031 := by
    have hnat : (5353852877 : ℕ)^5055*10000000000000^4031 ≤ 4568138106773^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353852877 10000000000 4568138106773 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566608383/5000000000 : ℝ)^5055 ≤ (8666615048483/20000000000000 : ℝ)^4031 := by
    have hnat : (2566608383 : ℕ)^5055*20000000000000^4031 ≤ 8666615048483^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566608383 5000000000 8666615048483 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429599713/2500000000 : ℝ)^5055 ≤ (10985543672577/100000000000000 : ℝ)^4031 := by
    have hnat : (429599713 : ℕ)^5055*100000000000000^4031 ≤ 10985543672577^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429599713 2500000000 10985543672577 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353852877/10000000000 : ℝ), (2566608383/5000000000 : ℝ), (-429599713/2500000000 : ℝ)] ![(4568138106773/10000000000000 : ℝ), (8666615048483/20000000000000 : ℝ), (10985543672577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353852877/10000000000 : ℝ)|^5055 ≤ (4568138106773/10000000000000 : ℝ)^4031
        have hw : |(5353852877/10000000000 : ℝ)|=(5353852877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566608383/5000000000 : ℝ)|^5055 ≤ (8666615048483/20000000000000 : ℝ)^4031
        have hw : |(2566608383/5000000000 : ℝ)|=(2566608383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429599713/2500000000 : ℝ)|^5055 ≤ (10985543672577/100000000000000 : ℝ)^4031
        have hw : |(-429599713/2500000000 : ℝ)|=(429599713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2073308773/5000000000 : ℝ)*x 0 + (3684112121/10000000000 : ℝ)*x 1 + (1161910139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073308773/5000000000 : ℝ)^5055 ≤ (6631416382521/20000000000000 : ℝ)^4031 := by
    have hnat : (2073308773 : ℕ)^5055*20000000000000^4031 ≤ 6631416382521^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073308773 5000000000 6631416382521 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3684112121/10000000000 : ℝ)^5055 ≤ (2858695016111/10000000000000 : ℝ)^4031 := by
    have hnat : (3684112121 : ℕ)^5055*10000000000000^4031 ≤ 2858695016111^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684112121 10000000000 2858695016111 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161910139/2500000000 : ℝ)^5055 ≤ (4781995989331/12500000000000 : ℝ)^4031 := by
    have hnat : (1161910139 : ℕ)^5055*12500000000000^4031 ≤ 4781995989331^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161910139 2500000000 4781995989331 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073308773/5000000000 : ℝ), (3684112121/10000000000 : ℝ), (1161910139/2500000000 : ℝ)] ![(6631416382521/20000000000000 : ℝ), (2858695016111/10000000000000 : ℝ), (4781995989331/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073308773/5000000000 : ℝ)|^5055 ≤ (6631416382521/20000000000000 : ℝ)^4031
        have hw : |(2073308773/5000000000 : ℝ)|=(2073308773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3684112121/10000000000 : ℝ)|^5055 ≤ (2858695016111/10000000000000 : ℝ)^4031
        have hw : |(3684112121/10000000000 : ℝ)|=(3684112121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161910139/2500000000 : ℝ)|^5055 ≤ (4781995989331/12500000000000 : ℝ)^4031
        have hw : |(1161910139/2500000000 : ℝ)|=(1161910139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-383166629/2500000000 : ℝ)*x 0 + (5137069611/10000000000 : ℝ)*x 1 + (219472749/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383166629/2500000000 : ℝ)^5055 ≤ (4758783212271/50000000000000 : ℝ)^4031 := by
    have hnat : (383166629 : ℕ)^5055*50000000000000^4031 ≤ 4758783212271^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383166629 2500000000 4758783212271 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137069611/10000000000 : ℝ)^5055 ≤ (542173324329/1250000000000 : ℝ)^4031 := by
    have hnat : (5137069611 : ℕ)^5055*1250000000000^4031 ≤ 542173324329^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137069611 10000000000 542173324329 1250000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219472749/400000000 : ℝ)^5055 ≤ (47108567620573/100000000000000 : ℝ)^4031 := by
    have hnat : (219472749 : ℕ)^5055*100000000000000^4031 ≤ 47108567620573^4031*400000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219472749 400000000 47108567620573 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383166629/2500000000 : ℝ), (5137069611/10000000000 : ℝ), (219472749/400000000 : ℝ)] ![(4758783212271/50000000000000 : ℝ), (542173324329/1250000000000 : ℝ), (47108567620573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383166629/2500000000 : ℝ)|^5055 ≤ (4758783212271/50000000000000 : ℝ)^4031
        have hw : |(-383166629/2500000000 : ℝ)|=(383166629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137069611/10000000000 : ℝ)|^5055 ≤ (542173324329/1250000000000 : ℝ)^4031
        have hw : |(5137069611/10000000000 : ℝ)|=(5137069611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219472749/400000000 : ℝ)|^5055 ≤ (47108567620573/100000000000000 : ℝ)^4031
        have hw : |(219472749/400000000 : ℝ)|=(219472749/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131460089/250000000 : ℝ)*x 0 + (-682398313/5000000000 : ℝ)*x 1 + (2743409779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131460089/250000000 : ℝ)^5055 ≤ (22331201284191/50000000000000 : ℝ)^4031 := by
    have hnat : (131460089 : ℕ)^5055*50000000000000^4031 ≤ 22331201284191^4031*250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131460089 250000000 22331201284191 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682398313/5000000000 : ℝ)^5055 ≤ (4114510410283/50000000000000 : ℝ)^4031 := by
    have hnat : (682398313 : ℕ)^5055*50000000000000^4031 ≤ 4114510410283^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682398313 5000000000 4114510410283 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743409779/5000000000 : ℝ)^5055 ≤ (23554288294669/50000000000000 : ℝ)^4031 := by
    have hnat : (2743409779 : ℕ)^5055*50000000000000^4031 ≤ 23554288294669^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743409779 5000000000 23554288294669 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131460089/250000000 : ℝ), (-682398313/5000000000 : ℝ), (2743409779/5000000000 : ℝ)] ![(22331201284191/50000000000000 : ℝ), (4114510410283/50000000000000 : ℝ), (23554288294669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131460089/250000000 : ℝ)|^5055 ≤ (22331201284191/50000000000000 : ℝ)^4031
        have hw : |(131460089/250000000 : ℝ)|=(131460089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-682398313/5000000000 : ℝ)|^5055 ≤ (4114510410283/50000000000000 : ℝ)^4031
        have hw : |(-682398313/5000000000 : ℝ)|=(682398313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743409779/5000000000 : ℝ)|^5055 ≤ (23554288294669/50000000000000 : ℝ)^4031
        have hw : |(2743409779/5000000000 : ℝ)|=(2743409779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629201953/5000000000 : ℝ)*x 0 + (5486818579/10000000000 : ℝ)*x 1 + (-682398767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629201953/5000000000 : ℝ)^5055 ≤ (558280078171/1250000000000 : ℝ)^4031 := by
    have hnat : (2629201953 : ℕ)^5055*1250000000000^4031 ≤ 558280078171^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629201953 5000000000 558280078171 1250000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486818579/10000000000 : ℝ)^5055 ≤ (5888570756077/12500000000000 : ℝ)^4031 := by
    have hnat : (5486818579 : ℕ)^5055*12500000000000^4031 ≤ 5888570756077^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486818579 10000000000 5888570756077 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682398767/5000000000 : ℝ)^5055 ≤ (8229027686103/100000000000000 : ℝ)^4031 := by
    have hnat : (682398767 : ℕ)^5055*100000000000000^4031 ≤ 8229027686103^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682398767 5000000000 8229027686103 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629201953/5000000000 : ℝ), (5486818579/10000000000 : ℝ), (-682398767/5000000000 : ℝ)] ![(558280078171/1250000000000 : ℝ), (5888570756077/12500000000000 : ℝ), (8229027686103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629201953/5000000000 : ℝ)|^5055 ≤ (558280078171/1250000000000 : ℝ)^4031
        have hw : |(2629201953/5000000000 : ℝ)|=(2629201953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486818579/10000000000 : ℝ)|^5055 ≤ (5888570756077/12500000000000 : ℝ)^4031
        have hw : |(5486818579/10000000000 : ℝ)|=(5486818579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682398767/5000000000 : ℝ)|^5055 ≤ (8229027686103/100000000000000 : ℝ)^4031
        have hw : |(-682398767/5000000000 : ℝ)|=(682398767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s4_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4147074161/10000000000 : ℝ)*x 0 + (463725821/1000000000 : ℝ)*x 1 + (461831021/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147074161/10000000000 : ℝ)^5055 ≤ (165808303313/500000000000 : ℝ)^4031 := by
    have hnat : (4147074161 : ℕ)^5055*500000000000^4031 ≤ 165808303313^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147074161 10000000000 165808303313 500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463725821/1000000000 : ℝ)^5055 ≤ (38148829008289/100000000000000 : ℝ)^4031 := by
    have hnat : (463725821 : ℕ)^5055*100000000000000^4031 ≤ 38148829008289^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463725821 1000000000 38148829008289 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461831021/1250000000 : ℝ)^5055 ≤ (5737902062923/20000000000000 : ℝ)^4031 := by
    have hnat : (461831021 : ℕ)^5055*20000000000000^4031 ≤ 5737902062923^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461831021 1250000000 5737902062923 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147074161/10000000000 : ℝ), (463725821/1000000000 : ℝ), (461831021/1250000000 : ℝ)] ![(165808303313/500000000000 : ℝ), (38148829008289/100000000000000 : ℝ), (5737902062923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147074161/10000000000 : ℝ)|^5055 ≤ (165808303313/500000000000 : ℝ)^4031
        have hw : |(4147074161/10000000000 : ℝ)|=(4147074161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463725821/1000000000 : ℝ)|^5055 ≤ (38148829008289/100000000000000 : ℝ)^4031
        have hw : |(463725821/1000000000 : ℝ)|=(463725821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461831021/1250000000 : ℝ)|^5055 ≤ (5737902062923/20000000000000 : ℝ)^4031
        have hw : |(461831021/1250000000 : ℝ)|=(461831021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9713/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1943/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (541/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9713/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9713/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9713/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9713/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9713/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9713/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9713/100000 : ℝ) ^ (5047/1024 : ℝ) ≤ (102083974704867/10000000000000000000 : ℝ) := by
    have hpowers : (9713/100000 : ℝ)^5047 ≤ (102083974704867/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9713 : ℕ)^5047*10000000000000000000^1024 ≤ 102083974704867^1024*100000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9713 100000 102083974704867 10000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9713/100000 : ℝ)) (X := (102083974704867/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17313/100000 : ℝ) ^ (5047/1024 : ℝ) ≤ (17626146188812593/100000000000000000000 : ℝ) := by
    have hpowers : (17313/100000 : ℝ)^5047 ≤ (17626146188812593/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17313 : ℕ)^5047*100000000000000000000^1024 ≤ 17626146188812593^1024*100000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17313 100000 17626146188812593 100000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17313/100000 : ℝ)) (X := (17626146188812593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000102083974704867/5000000000000000000 : ℝ) ≤ (10000041423871407/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (5000102083974704867/5000000000000000000 : ℝ)^1024 ≤ (10000041423871407/10000000000000000 : ℝ)^5047 := by
      have hnat : (5000102083974704867 : ℕ)^1024*10000000000000000^5047 ≤ 10000041423871407^5047*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000102083974704867 5000000000000000000 10000041423871407 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041423871407/10000000000000000 : ℝ)) (X := (5000102083974704867/5000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018646985935861263/100000000000000000000 : ℝ) ≤ (2500094576454757/2500000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (100018646985935861263/100000000000000000000 : ℝ)^1024 ≤ (2500094576454757/2500000000000000 : ℝ)^5047 := by
      have hnat : (100018646985935861263 : ℕ)^1024*2500000000000000^5047 ≤ 2500094576454757^5047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018646985935861263 100000000000000000000 2500094576454757 2500000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500094576454757/2500000000000000 : ℝ)) (X := (100018646985935861263/100000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017626146188812593/50000000000000000000 : ℝ) ≤ (10000715187766649/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (50017626146188812593/50000000000000000000 : ℝ)^1024 ≤ (10000715187766649/10000000000000000 : ℝ)^5047 := by
      have hnat : (50017626146188812593 : ℕ)^1024*10000000000000000^5047 ≤ 10000715187766649^5047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017626146188812593 50000000000000000000 10000715187766649 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000715187766649/10000000000000000 : ℝ)) (X := (50017626146188812593/50000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(102083974704867/10000000000000000000 : ℝ) ≤ ((37996885276354103827/38000000000000000000 : ℝ)+2*(336881947621/760000000000000 : ℝ)*(9713/100000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (37996885276354103827/38000000000000000000 : ℝ)+2*(336881947621/760000000000000 : ℝ)*(9713/100000 : ℝ)=(10000041423871407/10000000000000000 : ℝ) by norm_num, show 1+2*(102083974704867/10000000000000000000 : ℝ)=(5000102083974704867/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17626146188812593/100000000000000000000 : ℝ)+(102083974704867/10000000000000000000 : ℝ) ≤ ((37996885276354103827/38000000000000000000 : ℝ)+(336881947621/760000000000000 : ℝ)*((17313/100000 : ℝ)+(9713/100000 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (37996885276354103827/38000000000000000000 : ℝ)+(336881947621/760000000000000 : ℝ)*((17313/100000 : ℝ)+(9713/100000 : ℝ))=(2500094576454757/2500000000000000 : ℝ) by norm_num, show 1+(17626146188812593/100000000000000000000 : ℝ)+(102083974704867/10000000000000000000 : ℝ)=(100018646985935861263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17626146188812593/100000000000000000000 : ℝ) ≤ ((37996885276354103827/38000000000000000000 : ℝ)+2*(336881947621/760000000000000 : ℝ)*(17313/100000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (37996885276354103827/38000000000000000000 : ℝ)+2*(336881947621/760000000000000 : ℝ)*(17313/100000 : ℝ)=(10000715187766649/10000000000000000 : ℝ) by norm_num, show 1+2*(17626146188812593/100000000000000000000 : ℝ)=(50017626146188812593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37996885276354103827/38000000000000000000 : ℝ)*(X 1 0+X 2 0)+(336881947621/760000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (9713/100000 : ℝ)) (hi := (17313/100000 : ℝ)) (c := (37996885276354103827/38000000000000000000 : ℝ)) (alpha := (336881947621/760000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37996885276354103827/38000000000000000000 : ℝ)*(X 0 1+X 2 1)+(336881947621/760000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (9713/100000 : ℝ)) (hi := (17313/100000 : ℝ)) (c := (37996885276354103827/38000000000000000000 : ℝ)) (alpha := (336881947621/760000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37996885276354103827/38000000000000000000 : ℝ)*(X 0 2+X 1 2)+(336881947621/760000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (9713/100000 : ℝ)) (hi := (17313/100000 : ℝ)) (c := (37996885276354103827/38000000000000000000 : ℝ)) (alpha := (336881947621/760000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1532497137/10000000000 : ℝ)*X 0 0+(1372681999/2500000000 : ℝ)*X 0 1+(320826139/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669231649/1250000000 : ℝ)*X 1 0+(-859199781/5000000000 : ℝ)*X 1 1+(513321591/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353852877/10000000000 : ℝ)*X 2 0+(2566608383/5000000000 : ℝ)*X 2 1+(-429599713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2073308773/5000000000 : ℝ)*X 0 0+(3684112121/10000000000 : ℝ)*X 0 1+(1161910139/2500000000 : ℝ)*X 0 2+(2073308773/5000000000 : ℝ)*X 1 0+(3684112121/10000000000 : ℝ)*X 1 1+(1161910139/2500000000 : ℝ)*X 1 2+(2073308773/5000000000 : ℝ)*X 2 0+(3684112121/10000000000 : ℝ)*X 2 1+(1161910139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-383166629/2500000000 : ℝ)*X 0 0+(5137069611/10000000000 : ℝ)*X 0 1+(219472749/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((131460089/250000000 : ℝ)*X 1 0+(-682398313/5000000000 : ℝ)*X 1 1+(2743409779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629201953/5000000000 : ℝ)*X 2 0+(5486818579/10000000000 : ℝ)*X 2 1+(-682398767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4147074161/10000000000 : ℝ)*X 0 0+(463725821/1000000000 : ℝ)*X 0 1+(461831021/1250000000 : ℝ)*X 0 2+(4147074161/10000000000 : ℝ)*X 1 0+(463725821/1000000000 : ℝ)*X 1 1+(461831021/1250000000 : ℝ)*X 1 2+(4147074161/10000000000 : ℝ)*X 2 0+(463725821/1000000000 : ℝ)*X 2 1+(461831021/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (977088625438387750191579129/118750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (473697231/50000000000000 : ℝ)*(base19) + (802634443/100000000000000 : ℝ)*(base23) + (628159/2500000000000 : ℝ)*(lower2) + (97218517/100000000000000 : ℝ)*(upper5) + (239686202036809/12500000000000 : ℝ)*(major0) + (239686202036809/12500000000000 : ℝ)*(major1) + (239686202036809/12500000000000 : ℝ)*(major2) + (546313407099/19531250000 : ℝ)*(sp0) + (1398559215892887/50000000000000 : ℝ)*(sp1) + (559424464044793/20000000000000 : ℝ)*(sp2) + (25946337072491/2500000000000 : ℝ)*(sp3) + (1316291661/25000000000000 : ℝ)*(sp5) + (1521488473/100000000000000 : ℝ)*(sp6) + (33242877/4000000000000 : ℝ)*(sp7) + (207570862794313/20000000000000 : ℝ)*(f.failure) + (546313407099/19531250000 : ℝ)*(f.sum) + (10343455657639/4750000000000000000000000000 : ℝ)*base65 + (6552160793418781957/475000000000000000000000000000000 : ℝ)*base68 + (2350396858668781957/475000000000000000000000000000000 : ℝ)*base70 + (2560979678843781957/475000000000000000000000000000000 : ℝ)*base72 + (26861801669111/4750000000000000000000000000 : ℝ)*base74 + (2465986480368781957/475000000000000000000000000000000 : ℝ)*base76 + (68701263531218043/475000000000000000000000000000000 : ℝ)*base77 + (7622090967493781957/475000000000000000000000000000000 : ℝ)*base80 + (5209653039111/4750000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (24085653/2000000000000000000000 : ℝ)*base89 + (24085653/2000000000000000000000 : ℝ)*base91 + (24085653/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11755829870894141013586438491/950000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43557407/3125000000000 : ℝ)*(base19) + (791310029/50000000000000 : ℝ)*(base23) + (92400569/25000000000000 : ℝ)*(lower1) + (70320477/25000000000000 : ℝ)*(upper3) + (1835693/3125000000000 : ℝ)*(lower4) + (279385357/100000000000000 : ℝ)*(upper5) + (1960030777111211/100000000000000 : ℝ)*(major0) + (1960030777111211/100000000000000 : ℝ)*(major1) + (1960030777111211/100000000000000 : ℝ)*(major2) + (3059207757/50000000000000 : ℝ)*(sp1) + (2859181134744981/100000000000000 : ℝ)*(sp4) + (2859173622492443/100000000000000 : ℝ)*(sp5) + (1429589776062461/50000000000000 : ℝ)*(sp6) + (530440003496089/50000000000000 : ℝ)*(sp7) + (530440003496089/50000000000000 : ℝ)*(f.failure) + (2859181134744981/100000000000000 : ℝ)*(f.sum) + (70226151676969/38000000000000000000000000000 : ℝ)*base66 + (25648732536028745503/3800000000000000000000000000000000 : ℝ)*base68 + (21155404896428745503/3800000000000000000000000000000000 : ℝ)*base70 + (39714343825028745503/3800000000000000000000000000000000 : ℝ)*base72 + (28854184507031/38000000000000000000000000000 : ℝ)*base73 + (4301107990628745503/3800000000000000000000000000000000 : ℝ)*base76 + (11173408568228745503/3800000000000000000000000000000000 : ℝ)*base78 + (1602384365371254497/3800000000000000000000000000000000 : ℝ)*base79 + (100875266751031/38000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5987109/5000000000000000000000 : ℝ)*base89 + (5987109/5000000000000000000000 : ℝ)*base91 + (5987109/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1679_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9713/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1943/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (541/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1679_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1679_box_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1187772923/10000000000 : ℝ)*x 0 + (5434258687/10000000000 : ℝ)*x 1 + (2717128029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1187772923/10000000000 : ℝ)^5055 ≤ (1728330509587/25000000000000 : ℝ)^4031 := by
    have hnat : (1187772923 : ℕ)^5055*25000000000000^4031 ≤ 1728330509587^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187772923 10000000000 1728330509587 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434258687/10000000000 : ℝ)^5055 ≤ (11635838273341/25000000000000 : ℝ)^4031 := by
    have hnat : (5434258687 : ℕ)^5055*25000000000000^4031 ≤ 11635838273341^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434258687 10000000000 11635838273341 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717128029/5000000000 : ℝ)^5055 ≤ (727239450883/1562500000000 : ℝ)^4031 := by
    have hnat : (2717128029 : ℕ)^5055*1562500000000^4031 ≤ 727239450883^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717128029 5000000000 727239450883 1562500000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1187772923/10000000000 : ℝ), (5434258687/10000000000 : ℝ), (2717128029/5000000000 : ℝ)] ![(1728330509587/25000000000000 : ℝ), (11635838273341/25000000000000 : ℝ), (727239450883/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1187772923/10000000000 : ℝ)|^5055 ≤ (1728330509587/25000000000000 : ℝ)^4031
        have hw : |(-1187772923/10000000000 : ℝ)|=(1187772923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434258687/10000000000 : ℝ)|^5055 ≤ (11635838273341/25000000000000 : ℝ)^4031
        have hw : |(5434258687/10000000000 : ℝ)|=(5434258687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717128029/5000000000 : ℝ)|^5055 ≤ (727239450883/1562500000000 : ℝ)^4031
        have hw : |(2717128029/5000000000 : ℝ)|=(2717128029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653259749/1250000000 : ℝ)*x 0 + (-296752147/2000000000 : ℝ)*x 1 + (1358564693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653259749/1250000000 : ℝ)^5055 ≤ (22159183661219/50000000000000 : ℝ)^4031 := by
    have hnat : (653259749 : ℕ)^5055*50000000000000^4031 ≤ 22159183661219^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653259749 1250000000 22159183661219 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296752147/2000000000 : ℝ)^5055 ≤ (9138278652379/100000000000000 : ℝ)^4031 := by
    have hnat : (296752147 : ℕ)^5055*100000000000000^4031 ≤ 9138278652379^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296752147 2000000000 9138278652379 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358564693/2500000000 : ℝ)^5055 ≤ (46543354006309/100000000000000 : ℝ)^4031 := by
    have hnat : (1358564693 : ℕ)^5055*100000000000000^4031 ≤ 46543354006309^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358564693 2500000000 46543354006309 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653259749/1250000000 : ℝ), (-296752147/2000000000 : ℝ), (1358564693/2500000000 : ℝ)] ![(22159183661219/50000000000000 : ℝ), (9138278652379/100000000000000 : ℝ), (46543354006309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653259749/1250000000 : ℝ)|^5055 ≤ (22159183661219/50000000000000 : ℝ)^4031
        have hw : |(653259749/1250000000 : ℝ)|=(653259749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296752147/2000000000 : ℝ)|^5055 ≤ (9138278652379/100000000000000 : ℝ)^4031
        have hw : |(-296752147/2000000000 : ℝ)|=(296752147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358564693/2500000000 : ℝ)|^5055 ≤ (46543354006309/100000000000000 : ℝ)^4031
        have hw : |(1358564693/2500000000 : ℝ)|=(1358564693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226078789/10000000000 : ℝ)*x 0 + (5434257787/10000000000 : ℝ)*x 1 + (-1483761009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226078789/10000000000 : ℝ)^5055 ≤ (22159187899059/50000000000000 : ℝ)^4031 := by
    have hnat : (5226078789 : ℕ)^5055*50000000000000^4031 ≤ 22159187899059^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226078789 10000000000 22159187899059 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434257787/10000000000 : ℝ)^5055 ≤ (46543343426887/100000000000000 : ℝ)^4031 := by
    have hnat : (5434257787 : ℕ)^5055*100000000000000^4031 ≤ 46543343426887^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434257787 10000000000 46543343426887 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483761009/10000000000 : ℝ)^5055 ≤ (9138280768593/100000000000000 : ℝ)^4031 := by
    have hnat : (1483761009 : ℕ)^5055*100000000000000^4031 ≤ 9138280768593^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483761009 10000000000 9138280768593 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226078789/10000000000 : ℝ), (5434257787/10000000000 : ℝ), (-1483761009/10000000000 : ℝ)] ![(22159187899059/50000000000000 : ℝ), (46543343426887/100000000000000 : ℝ), (9138280768593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226078789/10000000000 : ℝ)|^5055 ≤ (22159187899059/50000000000000 : ℝ)^4031
        have hw : |(5226078789/10000000000 : ℝ)|=(5226078789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434257787/10000000000 : ℝ)|^5055 ≤ (46543343426887/100000000000000 : ℝ)^4031
        have hw : |(5434257787/10000000000 : ℝ)|=(5434257787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1483761009/10000000000 : ℝ)|^5055 ≤ (9138280768593/100000000000000 : ℝ)^4031
        have hw : |(-1483761009/10000000000 : ℝ)|=(1483761009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (141642673/312500000 : ℝ)*x 0 + (994221807/2500000000 : ℝ)*x 1 + (397688619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141642673/312500000 : ℝ)^5055 ≤ (7414378374807/20000000000000 : ℝ)^4031 := by
    have hnat : (141642673 : ℕ)^5055*20000000000000^4031 ≤ 7414378374807^4031*312500000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141642673 312500000 7414378374807 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994221807/2500000000 : ℝ)^5055 ≤ (15732029604151/50000000000000 : ℝ)^4031 := by
    have hnat : (994221807 : ℕ)^5055*50000000000000^4031 ≤ 15732029604151^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994221807 2500000000 15732029604151 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397688619/1000000000 : ℝ)^5055 ≤ (15732024454863/50000000000000 : ℝ)^4031 := by
    have hnat : (397688619 : ℕ)^5055*50000000000000^4031 ≤ 15732024454863^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397688619 1000000000 15732024454863 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(141642673/312500000 : ℝ), (994221807/2500000000 : ℝ), (397688619/1000000000 : ℝ)] ![(7414378374807/20000000000000 : ℝ), (15732029604151/50000000000000 : ℝ), (15732024454863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(141642673/312500000 : ℝ)|^5055 ≤ (7414378374807/20000000000000 : ℝ)^4031
        have hw : |(141642673/312500000 : ℝ)|=(141642673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994221807/2500000000 : ℝ)|^5055 ≤ (15732029604151/50000000000000 : ℝ)^4031
        have hw : |(994221807/2500000000 : ℝ)|=(994221807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397688619/1000000000 : ℝ)|^5055 ≤ (15732024454863/50000000000000 : ℝ)^4031
        have hw : |(397688619/1000000000 : ℝ)|=(397688619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-949177201/5000000000 : ℝ)*x 0 + (517506461/1000000000 : ℝ)*x 1 + (5175062639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (949177201/5000000000 : ℝ)^5055 ≤ (2489387850559/20000000000000 : ℝ)^4031 := by
    have hnat : (949177201 : ℕ)^5055*20000000000000^4031 ≤ 2489387850559^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949177201 5000000000 2489387850559 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517506461/1000000000 : ℝ)^5055 ≤ (43776540823887/100000000000000 : ℝ)^4031 := by
    have hnat : (517506461 : ℕ)^5055*100000000000000^4031 ≤ 43776540823887^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517506461 1000000000 43776540823887 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175062639/10000000000 : ℝ)^5055 ≤ (8755303983099/20000000000000 : ℝ)^4031 := by
    have hnat : (5175062639 : ℕ)^5055*20000000000000^4031 ≤ 8755303983099^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175062639 10000000000 8755303983099 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-949177201/5000000000 : ℝ), (517506461/1000000000 : ℝ), (5175062639/10000000000 : ℝ)] ![(2489387850559/20000000000000 : ℝ), (43776540823887/100000000000000 : ℝ), (8755303983099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-949177201/5000000000 : ℝ)|^5055 ≤ (2489387850559/20000000000000 : ℝ)^4031
        have hw : |(-949177201/5000000000 : ℝ)|=(949177201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517506461/1000000000 : ℝ)|^5055 ≤ (43776540823887/100000000000000 : ℝ)^4031
        have hw : |(517506461/1000000000 : ℝ)|=(517506461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175062639/10000000000 : ℝ)|^5055 ≤ (8755303983099/20000000000000 : ℝ)^4031
        have hw : |(5175062639/10000000000 : ℝ)|=(5175062639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403215211/10000000000 : ℝ)*x 0 + (-1595995657/10000000000 : ℝ)*x 1 + (5175064231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403215211/10000000000 : ℝ)^5055 ≤ (46210171972339/100000000000000 : ℝ)^4031 := by
    have hnat : (5403215211 : ℕ)^5055*100000000000000^4031 ≤ 46210171972339^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403215211 10000000000 46210171972339 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1595995657/10000000000 : ℝ)^5055 ≤ (10013291215937/100000000000000 : ℝ)^4031 := by
    have hnat : (1595995657 : ℕ)^5055*100000000000000^4031 ≤ 10013291215937^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595995657 10000000000 10013291215937 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175064231/10000000000 : ℝ)^5055 ≤ (875530736069/2000000000000 : ℝ)^4031 := by
    have hnat : (5175064231 : ℕ)^5055*2000000000000^4031 ≤ 875530736069^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175064231 10000000000 875530736069 2000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403215211/10000000000 : ℝ), (-1595995657/10000000000 : ℝ), (5175064231/10000000000 : ℝ)] ![(46210171972339/100000000000000 : ℝ), (10013291215937/100000000000000 : ℝ), (875530736069/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403215211/10000000000 : ℝ)|^5055 ≤ (46210171972339/100000000000000 : ℝ)^4031
        have hw : |(5403215211/10000000000 : ℝ)|=(5403215211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1595995657/10000000000 : ℝ)|^5055 ≤ (10013291215937/100000000000000 : ℝ)^4031
        have hw : |(-1595995657/10000000000 : ℝ)|=(1595995657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175064231/10000000000 : ℝ)|^5055 ≤ (875530736069/2000000000000 : ℝ)^4031
        have hw : |(5175064231/10000000000 : ℝ)|=(5175064231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403215701/10000000000 : ℝ)*x 0 + (5175063907/10000000000 : ℝ)*x 1 + (-797997713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403215701/10000000000 : ℝ)^5055 ≤ (9242035445509/20000000000000 : ℝ)^4031 := by
    have hnat : (5403215701 : ℕ)^5055*20000000000000^4031 ≤ 9242035445509^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403215701 10000000000 9242035445509 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175063907/10000000000 : ℝ)^5055 ≤ (21888266683227/50000000000000 : ℝ)^4031 := by
    have hnat : (5175063907 : ℕ)^5055*50000000000000^4031 ≤ 21888266683227^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175063907 10000000000 21888266683227 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797997713/5000000000 : ℝ)^5055 ≤ (5006644699237/50000000000000 : ℝ)^4031 := by
    have hnat : (797997713 : ℕ)^5055*50000000000000^4031 ≤ 5006644699237^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797997713 5000000000 5006644699237 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403215701/10000000000 : ℝ), (5175063907/10000000000 : ℝ), (-797997713/5000000000 : ℝ)] ![(9242035445509/20000000000000 : ℝ), (21888266683227/50000000000000 : ℝ), (5006644699237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403215701/10000000000 : ℝ)|^5055 ≤ (9242035445509/20000000000000 : ℝ)^4031
        have hw : |(5403215701/10000000000 : ℝ)|=(5403215701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175063907/10000000000 : ℝ)|^5055 ≤ (21888266683227/50000000000000 : ℝ)^4031
        have hw : |(5175063907/10000000000 : ℝ)|=(5175063907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-797997713/5000000000 : ℝ)|^5055 ≤ (5006644699237/50000000000000 : ℝ)^4031
        have hw : |(-797997713/5000000000 : ℝ)|=(797997713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (468339659/1250000000 : ℝ)*x 0 + (2184464251/5000000000 : ℝ)*x 1 + (2184464013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468339659/1250000000 : ℝ)^5055 ≤ (14598725220757/50000000000000 : ℝ)^4031 := by
    have hnat : (468339659 : ℕ)^5055*50000000000000^4031 ≤ 14598725220757^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468339659 1250000000 14598725220757 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184464251/5000000000 : ℝ)^5055 ≤ (7080255437493/20000000000000 : ℝ)^4031 := by
    have hnat : (2184464251 : ℕ)^5055*20000000000000^4031 ≤ 7080255437493^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184464251 5000000000 7080255437493 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184464013/5000000000 : ℝ)^5055 ≤ (8850318087663/25000000000000 : ℝ)^4031 := by
    have hnat : (2184464013 : ℕ)^5055*25000000000000^4031 ≤ 8850318087663^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184464013 5000000000 8850318087663 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(468339659/1250000000 : ℝ), (2184464251/5000000000 : ℝ), (2184464013/5000000000 : ℝ)] ![(14598725220757/50000000000000 : ℝ), (7080255437493/20000000000000 : ℝ), (8850318087663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(468339659/1250000000 : ℝ)|^5055 ≤ (14598725220757/50000000000000 : ℝ)^4031
        have hw : |(468339659/1250000000 : ℝ)|=(468339659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2184464251/5000000000 : ℝ)|^5055 ≤ (7080255437493/20000000000000 : ℝ)^4031
        have hw : |(2184464251/5000000000 : ℝ)|=(2184464251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184464013/5000000000 : ℝ)|^5055 ≤ (8850318087663/25000000000000 : ℝ)^4031
        have hw : |(2184464013/5000000000 : ℝ)|=(2184464013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_8 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109133099/625000000 : ℝ)*x 0 + (1246370329/2500000000 : ℝ)*x 1 + (684786789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109133099/625000000 : ℝ)^5055 ≤ (700519486007/6250000000000 : ℝ)^4031 := by
    have hnat : (109133099 : ℕ)^5055*6250000000000^4031 ≤ 700519486007^4031*625000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109133099 625000000 700519486007 6250000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246370329/2500000000 : ℝ)^5055 ≤ (20887441663249/50000000000000 : ℝ)^4031 := by
    have hnat : (1246370329 : ℕ)^5055*50000000000000^4031 ≤ 20887441663249^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246370329 2500000000 20887441663249 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684786789/1250000000 : ℝ)^5055 ≤ (47016804877133/100000000000000 : ℝ)^4031 := by
    have hnat : (684786789 : ℕ)^5055*100000000000000^4031 ≤ 47016804877133^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684786789 1250000000 47016804877133 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109133099/625000000 : ℝ), (1246370329/2500000000 : ℝ), (684786789/1250000000 : ℝ)] ![(700519486007/6250000000000 : ℝ), (20887441663249/50000000000000 : ℝ), (47016804877133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109133099/625000000 : ℝ)|^5055 ≤ (700519486007/6250000000000 : ℝ)^4031
        have hw : |(-109133099/625000000 : ℝ)|=(109133099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246370329/2500000000 : ℝ)|^5055 ≤ (20887441663249/50000000000000 : ℝ)^4031
        have hw : |(1246370329/2500000000 : ℝ)|=(1246370329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684786789/1250000000 : ℝ)|^5055 ≤ (47016804877133/100000000000000 : ℝ)^4031
        have hw : |(684786789/1250000000 : ℝ)|=(684786789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_9 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195989593/10000000000 : ℝ)*x 0 + (-7319123/50000000 : ℝ)*x 1 + (1369573589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195989593/10000000000 : ℝ)^5055 ≤ (43998627192837/100000000000000 : ℝ)^4031 := by
    have hnat : (5195989593 : ℕ)^5055*100000000000000^4031 ≤ 43998627192837^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195989593 10000000000 43998627192837 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7319123/50000000 : ℝ)^5055 ≤ (8984567439021/100000000000000 : ℝ)^4031 := by
    have hnat : (7319123 : ℕ)^5055*100000000000000^4031 ≤ 8984567439021^4031*50000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7319123 50000000 8984567439021 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369573589/2500000000 : ℝ)^5055 ≤ (47016805350687/100000000000000 : ℝ)^4031 := by
    have hnat : (1369573589 : ℕ)^5055*100000000000000^4031 ≤ 47016805350687^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369573589 2500000000 47016805350687 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195989593/10000000000 : ℝ), (-7319123/50000000 : ℝ), (1369573589/2500000000 : ℝ)] ![(43998627192837/100000000000000 : ℝ), (8984567439021/100000000000000 : ℝ), (47016805350687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195989593/10000000000 : ℝ)|^5055 ≤ (43998627192837/100000000000000 : ℝ)^4031
        have hw : |(5195989593/10000000000 : ℝ)|=(5195989593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7319123/50000000 : ℝ)|^5055 ≤ (8984567439021/100000000000000 : ℝ)^4031
        have hw : |(-7319123/50000000 : ℝ)|=(7319123/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369573589/2500000000 : ℝ)|^5055 ≤ (47016805350687/100000000000000 : ℝ)^4031
        have hw : |(1369573589/2500000000 : ℝ)|=(1369573589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_10 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649498699/1250000000 : ℝ)*x 0 + (547829447/1000000000 : ℝ)*x 1 + (-731912221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649498699/1250000000 : ℝ)^5055 ≤ (21999313591109/50000000000000 : ℝ)^4031 := by
    have hnat : (649498699 : ℕ)^5055*50000000000000^4031 ≤ 21999313591109^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649498699 1250000000 21999313591109 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547829447/1000000000 : ℝ)^5055 ≤ (2350840328881/5000000000000 : ℝ)^4031 := by
    have hnat : (547829447 : ℕ)^5055*5000000000000^4031 ≤ 2350840328881^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547829447 1000000000 2350840328881 5000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731912221/5000000000 : ℝ)^5055 ≤ (8984566222909/100000000000000 : ℝ)^4031 := by
    have hnat : (731912221 : ℕ)^5055*100000000000000^4031 ≤ 8984566222909^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731912221 5000000000 8984566222909 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649498699/1250000000 : ℝ), (547829447/1000000000 : ℝ), (-731912221/5000000000 : ℝ)] ![(21999313591109/50000000000000 : ℝ), (2350840328881/5000000000000 : ℝ), (8984566222909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649498699/1250000000 : ℝ)|^5055 ≤ (21999313591109/50000000000000 : ℝ)^4031
        have hw : |(649498699/1250000000 : ℝ)|=(649498699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547829447/1000000000 : ℝ)|^5055 ≤ (2350840328881/5000000000000 : ℝ)^4031
        have hw : |(547829447/1000000000 : ℝ)|=(547829447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-731912221/5000000000 : ℝ)|^5055 ≤ (8984566222909/100000000000000 : ℝ)^4031
        have hw : |(-731912221/5000000000 : ℝ)|=(731912221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_11 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4661027213/10000000000 : ℝ)*x 0 + (3910105869/10000000000 : ℝ)*x 1 + (1955052649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4661027213/10000000000 : ℝ)^5055 ≤ (38394199058253/100000000000000 : ℝ)^4031 := by
    have hnat : (4661027213 : ℕ)^5055*100000000000000^4031 ≤ 38394199058253^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661027213 10000000000 38394199058253 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3910105869/10000000000 : ℝ)^5055 ≤ (30802903287733/100000000000000 : ℝ)^4031 := by
    have hnat : (3910105869 : ℕ)^5055*100000000000000^4031 ≤ 30802903287733^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3910105869 10000000000 30802903287733 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955052649/5000000000 : ℝ)^5055 ≤ (7700724411711/25000000000000 : ℝ)^4031 := by
    have hnat : (1955052649 : ℕ)^5055*25000000000000^4031 ≤ 7700724411711^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955052649 5000000000 7700724411711 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4661027213/10000000000 : ℝ), (3910105869/10000000000 : ℝ), (1955052649/5000000000 : ℝ)] ![(38394199058253/100000000000000 : ℝ), (30802903287733/100000000000000 : ℝ), (7700724411711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4661027213/10000000000 : ℝ)|^5055 ≤ (38394199058253/100000000000000 : ℝ)^4031
        have hw : |(4661027213/10000000000 : ℝ)|=(4661027213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3910105869/10000000000 : ℝ)|^5055 ≤ (30802903287733/100000000000000 : ℝ)^4031
        have hw : |(3910105869/10000000000 : ℝ)|=(3910105869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1955052649/5000000000 : ℝ)|^5055 ≤ (7700724411711/25000000000000 : ℝ)^4031
        have hw : |(1955052649/5000000000 : ℝ)|=(1955052649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_12 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-166949997/1250000000 : ℝ)*x 0 + (112283163/200000000 : ℝ)*x 1 + (41197501/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166949997/1250000000 : ℝ)^5055 ≤ (4004431636267/50000000000000 : ℝ)^4031 := by
    have hnat : (166949997 : ℕ)^5055*50000000000000^4031 ≤ 4004431636267^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166949997 1250000000 4004431636267 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112283163/200000000 : ℝ)^5055 ≤ (6060453423401/12500000000000 : ℝ)^4031 := by
    have hnat : (112283163 : ℕ)^5055*12500000000000^4031 ≤ 6060453423401^4031*200000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112283163 200000000 6060453423401 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41197501/80000000 : ℝ)^5055 ≤ (43507509322371/100000000000000 : ℝ)^4031 := by
    have hnat : (41197501 : ℕ)^5055*100000000000000^4031 ≤ 43507509322371^4031*80000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41197501 80000000 43507509322371 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166949997/1250000000 : ℝ), (112283163/200000000 : ℝ), (41197501/80000000 : ℝ)] ![(4004431636267/50000000000000 : ℝ), (6060453423401/12500000000000 : ℝ), (43507509322371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166949997/1250000000 : ℝ)|^5055 ≤ (4004431636267/50000000000000 : ℝ)^4031
        have hw : |(-166949997/1250000000 : ℝ)|=(166949997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112283163/200000000 : ℝ)|^5055 ≤ (6060453423401/12500000000000 : ℝ)^4031
        have hw : |(112283163/200000000 : ℝ)|=(112283163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41197501/80000000 : ℝ)|^5055 ≤ (43507509322371/100000000000000 : ℝ)^4031
        have hw : |(41197501/80000000 : ℝ)|=(41197501/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_13 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710291331/5000000000 : ℝ)*x 0 + (-803247783/5000000000 : ℝ)*x 1 + (1029937657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710291331/5000000000 : ℝ)^5055 ≤ (11599128078987/25000000000000 : ℝ)^4031 := by
    have hnat : (2710291331 : ℕ)^5055*25000000000000^4031 ≤ 11599128078987^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710291331 5000000000 11599128078987 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803247783/5000000000 : ℝ)^5055 ≤ (10095971355791/100000000000000 : ℝ)^4031 := by
    have hnat : (803247783 : ℕ)^5055*100000000000000^4031 ≤ 10095971355791^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803247783 5000000000 10095971355791 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029937657/2000000000 : ℝ)^5055 ≤ (21753758157461/50000000000000 : ℝ)^4031 := by
    have hnat : (1029937657 : ℕ)^5055*50000000000000^4031 ≤ 21753758157461^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029937657 2000000000 21753758157461 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710291331/5000000000 : ℝ), (-803247783/5000000000 : ℝ), (1029937657/2000000000 : ℝ)] ![(11599128078987/25000000000000 : ℝ), (10095971355791/100000000000000 : ℝ), (21753758157461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710291331/5000000000 : ℝ)|^5055 ≤ (11599128078987/25000000000000 : ℝ)^4031
        have hw : |(2710291331/5000000000 : ℝ)|=(2710291331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-803247783/5000000000 : ℝ)|^5055 ≤ (10095971355791/100000000000000 : ℝ)^4031
        have hw : |(-803247783/5000000000 : ℝ)|=(803247783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029937657/2000000000 : ℝ)|^5055 ≤ (21753758157461/50000000000000 : ℝ)^4031
        have hw : |(1029937657/2000000000 : ℝ)|=(1029937657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_14 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420582517/10000000000 : ℝ)*x 0 + (2574844007/5000000000 : ℝ)*x 1 + (-1606496127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420582517/10000000000 : ℝ)^5055 ≤ (46396510759567/100000000000000 : ℝ)^4031 := by
    have hnat : (5420582517 : ℕ)^5055*100000000000000^4031 ≤ 46396510759567^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420582517 10000000000 46396510759567 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574844007/5000000000 : ℝ)^5055 ≤ (21753756721869/50000000000000 : ℝ)^4031 := by
    have hnat : (2574844007 : ℕ)^5055*50000000000000^4031 ≤ 21753756721869^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574844007 5000000000 21753756721869 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1606496127/10000000000 : ℝ)^5055 ≤ (2523993944247/25000000000000 : ℝ)^4031 := by
    have hnat : (1606496127 : ℕ)^5055*25000000000000^4031 ≤ 2523993944247^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606496127 10000000000 2523993944247 25000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420582517/10000000000 : ℝ), (2574844007/5000000000 : ℝ), (-1606496127/10000000000 : ℝ)] ![(46396510759567/100000000000000 : ℝ), (21753756721869/50000000000000 : ℝ), (2523993944247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420582517/10000000000 : ℝ)|^5055 ≤ (46396510759567/100000000000000 : ℝ)^4031
        have hw : |(5420582517/10000000000 : ℝ)|=(5420582517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574844007/5000000000 : ℝ)|^5055 ≤ (21753756721869/50000000000000 : ℝ)^4031
        have hw : |(2574844007/5000000000 : ℝ)|=(2574844007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1606496127/10000000000 : ℝ)|^5055 ≤ (2523993944247/25000000000000 : ℝ)^4031
        have hw : |(-1606496127/10000000000 : ℝ)|=(1606496127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_box_15 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3666803391/10000000000 : ℝ)*x 0 + (1101802509/2500000000 : ℝ)*x 1 + (4407207169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3666803391/10000000000 : ℝ)^5055 ≤ (14209312506291/50000000000000 : ℝ)^4031 := by
    have hnat : (3666803391 : ℕ)^5055*50000000000000^4031 ≤ 14209312506291^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666803391 10000000000 14209312506291 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101802509/2500000000 : ℝ)^5055 ≤ (7158140416931/20000000000000 : ℝ)^4031 := by
    have hnat : (1101802509 : ℕ)^5055*20000000000000^4031 ≤ 7158140416931^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101802509 2500000000 7158140416931 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4407207169/10000000000 : ℝ)^5055 ≤ (35790672887369/100000000000000 : ℝ)^4031 := by
    have hnat : (4407207169 : ℕ)^5055*100000000000000^4031 ≤ 35790672887369^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407207169 10000000000 35790672887369 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3666803391/10000000000 : ℝ), (1101802509/2500000000 : ℝ), (4407207169/10000000000 : ℝ)] ![(14209312506291/50000000000000 : ℝ), (7158140416931/20000000000000 : ℝ), (35790672887369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3666803391/10000000000 : ℝ)|^5055 ≤ (14209312506291/50000000000000 : ℝ)^4031
        have hw : |(3666803391/10000000000 : ℝ)|=(3666803391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101802509/2500000000 : ℝ)|^5055 ≤ (7158140416931/20000000000000 : ℝ)^4031
        have hw : |(1101802509/2500000000 : ℝ)|=(1101802509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4407207169/10000000000 : ℝ)|^5055 ≤ (35790672887369/100000000000000 : ℝ)^4031
        have hw : |(4407207169/10000000000 : ℝ)|=(4407207169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1943/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66489/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57667/100000 : ℝ) ∧ (10051/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44983/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1943/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1943/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1943/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1943/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1943/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1943/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1943/20000 : ℝ) ^ (5047/1024 : ℝ) ≤ (204375236943741/20000000000000000000 : ℝ) := by
    have hpowers : (1943/20000 : ℝ)^5047 ≤ (204375236943741/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1943 : ℕ)^5047*20000000000000000000^1024 ≤ 204375236943741^1024*20000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1943 20000 204375236943741 20000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1943/20000 : ℝ)) (X := (204375236943741/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (541/3125 : ℝ) ^ (5047/1024 : ℝ) ≤ (17621128899884891/100000000000000000000 : ℝ) := by
    have hpowers : (541/3125 : ℝ)^5047 ≤ (17621128899884891/100000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^5047*100000000000000000000^1024 ≤ 17621128899884891^1024*3125^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 3125 17621128899884891 100000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/3125 : ℝ)) (X := (17621128899884891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000204375236943741/10000000000000000000 : ℝ) ≤ (156250647905123/156250000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (10000204375236943741/10000000000000000000 : ℝ)^1024 ≤ (156250647905123/156250000000000 : ℝ)^5047 := by
      have hnat : (10000204375236943741 : ℕ)^1024*156250000000000^5047 ≤ 156250647905123^5047*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000204375236943741 10000000000000000000 156250647905123 156250000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250647905123/156250000000000 : ℝ)) (X := (10000204375236943741/10000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004660751271150899/25000000000000000000 : ℝ) ≤ (10000378225062421/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (25004660751271150899/25000000000000000000 : ℝ)^1024 ≤ (10000378225062421/10000000000000000 : ℝ)^5047 := by
      have hnat : (25004660751271150899 : ℕ)^1024*10000000000000000^5047 ≤ 10000378225062421^5047*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004660751271150899 25000000000000000000 10000378225062421 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000378225062421/10000000000000000 : ℝ)) (X := (25004660751271150899/25000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017621128899884891/50000000000000000000 : ℝ) ≤ (1000071498419697/1000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (50017621128899884891/50000000000000000000 : ℝ)^1024 ≤ (1000071498419697/1000000000000000 : ℝ)^5047 := by
      have hnat : (50017621128899884891 : ℕ)^1024*1000000000000000^5047 ≤ 1000071498419697^5047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017621128899884891 50000000000000000000 1000071498419697 1000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071498419697/1000000000000000 : ℝ)) (X := (50017621128899884891/50000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(204375236943741/20000000000000000000 : ℝ) ≤ ((37981885893334878257/37985000000000000000 : ℝ)+2*(336759134549/759700000000000 : ℝ)*(1943/20000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (37981885893334878257/37985000000000000000 : ℝ)+2*(336759134549/759700000000000 : ℝ)*(1943/20000 : ℝ)=(156250647905123/156250000000000 : ℝ) by norm_num, show 1+2*(204375236943741/20000000000000000000 : ℝ)=(10000204375236943741/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17621128899884891/100000000000000000000 : ℝ)+(204375236943741/20000000000000000000 : ℝ) ≤ ((37981885893334878257/37985000000000000000 : ℝ)+(336759134549/759700000000000 : ℝ)*((541/3125 : ℝ)+(1943/20000 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (37981885893334878257/37985000000000000000 : ℝ)+(336759134549/759700000000000 : ℝ)*((541/3125 : ℝ)+(1943/20000 : ℝ))=(10000378225062421/10000000000000000 : ℝ) by norm_num, show 1+(17621128899884891/100000000000000000000 : ℝ)+(204375236943741/20000000000000000000 : ℝ)=(25004660751271150899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17621128899884891/100000000000000000000 : ℝ) ≤ ((37981885893334878257/37985000000000000000 : ℝ)+2*(336759134549/759700000000000 : ℝ)*(541/3125 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (37981885893334878257/37985000000000000000 : ℝ)+2*(336759134549/759700000000000 : ℝ)*(541/3125 : ℝ)=(1000071498419697/1000000000000000 : ℝ) by norm_num, show 1+2*(17621128899884891/100000000000000000000 : ℝ)=(50017621128899884891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37981885893334878257/37985000000000000000 : ℝ)*(X 1 0+X 2 0)+(336759134549/759700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1943/20000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (37981885893334878257/37985000000000000000 : ℝ)) (alpha := (336759134549/759700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37981885893334878257/37985000000000000000 : ℝ)*(X 0 1+X 2 1)+(336759134549/759700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1943/20000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (37981885893334878257/37985000000000000000 : ℝ)) (alpha := (336759134549/759700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37981885893334878257/37985000000000000000 : ℝ)*(X 0 2+X 1 2)+(336759134549/759700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1943/20000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (37981885893334878257/37985000000000000000 : ℝ)) (alpha := (336759134549/759700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1187772923/10000000000 : ℝ)*X 0 0+(5434258687/10000000000 : ℝ)*X 0 1+(2717128029/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653259749/1250000000 : ℝ)*X 1 0+(-296752147/2000000000 : ℝ)*X 1 1+(1358564693/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226078789/10000000000 : ℝ)*X 2 0+(5434257787/10000000000 : ℝ)*X 2 1+(-1483761009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((141642673/312500000 : ℝ)*X 0 0+(994221807/2500000000 : ℝ)*X 0 1+(397688619/1000000000 : ℝ)*X 0 2+(141642673/312500000 : ℝ)*X 1 0+(994221807/2500000000 : ℝ)*X 1 1+(397688619/1000000000 : ℝ)*X 1 2+(141642673/312500000 : ℝ)*X 2 0+(994221807/2500000000 : ℝ)*X 2 1+(397688619/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-949177201/5000000000 : ℝ)*X 0 0+(517506461/1000000000 : ℝ)*X 0 1+(5175062639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5403215211/10000000000 : ℝ)*X 1 0+(-1595995657/10000000000 : ℝ)*X 1 1+(5175064231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5403215701/10000000000 : ℝ)*X 2 0+(5175063907/10000000000 : ℝ)*X 2 1+(-797997713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((468339659/1250000000 : ℝ)*X 0 0+(2184464251/5000000000 : ℝ)*X 0 1+(2184464013/5000000000 : ℝ)*X 0 2+(468339659/1250000000 : ℝ)*X 1 0+(2184464251/5000000000 : ℝ)*X 1 1+(2184464013/5000000000 : ℝ)*X 1 2+(468339659/1250000000 : ℝ)*X 2 0+(2184464251/5000000000 : ℝ)*X 2 1+(2184464013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-109133099/625000000 : ℝ)*X 0 0+(1246370329/2500000000 : ℝ)*X 0 1+(684786789/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5195989593/10000000000 : ℝ)*X 1 0+(-7319123/50000000 : ℝ)*X 1 1+(1369573589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((649498699/1250000000 : ℝ)*X 2 0+(547829447/1000000000 : ℝ)*X 2 1+(-731912221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4661027213/10000000000 : ℝ)*X 0 0+(3910105869/10000000000 : ℝ)*X 0 1+(1955052649/5000000000 : ℝ)*X 0 2+(4661027213/10000000000 : ℝ)*X 1 0+(3910105869/10000000000 : ℝ)*X 1 1+(1955052649/5000000000 : ℝ)*X 1 2+(4661027213/10000000000 : ℝ)*X 2 0+(3910105869/10000000000 : ℝ)*X 2 1+(1955052649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-166949997/1250000000 : ℝ)*X 0 0+(112283163/200000000 : ℝ)*X 0 1+(41197501/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2710291331/5000000000 : ℝ)*X 1 0+(-803247783/5000000000 : ℝ)*X 1 1+(1029937657/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5420582517/10000000000 : ℝ)*X 2 0+(2574844007/5000000000 : ℝ)*X 2 1+(-1606496127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3666803391/10000000000 : ℝ)*X 0 0+(1101802509/2500000000 : ℝ)*X 0 1+(4407207169/10000000000 : ℝ)*X 0 2+(3666803391/10000000000 : ℝ)*X 1 0+(1101802509/2500000000 : ℝ)*X 1 1+(4407207169/10000000000 : ℝ)*X 1 2+(3666803391/10000000000 : ℝ)*X 2 0+(1101802509/2500000000 : ℝ)*X 2 1+(4407207169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66489/100000 : ℝ) ≤ (-631370689336138147235605729189071/949625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10658179/100000000000000 : ℝ)*(upper0) + (2611523/100000000000000 : ℝ)*(lower1) + (88015487/100000000000000 : ℝ)*(lower2) + (638500442312233/50000000000000 : ℝ)*(major0) + (638500442312233/50000000000000 : ℝ)*(major1) + (638500442312233/50000000000000 : ℝ)*(major2) + (548407759/25000000000000 : ℝ)*(sp3) + (1884970069060497/100000000000000 : ℝ)*(sp4) + (117810084932181/6250000000000 : ℝ)*(sp5) + (1884963862178661/100000000000000 : ℝ)*(sp6) + (691183232245853/100000000000000 : ℝ)*(sp7) + (2095007933/25000000000000 : ℝ)*(sp8) + (17090177333/100000000000000 : ℝ)*(sp13) + (455841049/3125000000000 : ℝ)*(sp14) + (86398178234611/12500000000000 : ℝ)*(f.failure) + (1884978449092229/100000000000000 : ℝ)*(f.sum) + (7244878650321/9496250000000000000000000000 : ℝ)*base65 + (8258230246195332119/1899250000000000000000000000000000 : ℝ)*base68 + (2836266709228582119/1899250000000000000000000000000000 : ℝ)*base70 + (10219188622206832119/1899250000000000000000000000000000 : ℝ)*base72 + (101709533891103/18992500000000000000000000000 : ℝ)*base74 + (6510838584143082119/1899250000000000000000000000000000 : ℝ)*base76 + (3735839528070582119/1899250000000000000000000000000000 : ℝ)*base78 + (11987278466497582119/1899250000000000000000000000000000 : ℝ)*base80 + (8688352886363/18992500000000000000000000000 : ℝ)*base82 + (9230409/1250000000000000000000 : ℝ)*base90 + (9230409/1250000000000000000000 : ℝ)*base92 + (9230409/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (57667/100000 : ℝ) ≤ (136910483040553401804205023865557/237406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9080157/25000000000000 : ℝ)*(lower1) + (10004167/10000000000000 : ℝ)*(lower2) + (32756153/25000000000000 : ℝ)*(lower5) + (171612618519739/12500000000000 : ℝ)*(major0) + (171612618519739/12500000000000 : ℝ)*(major1) + (171612618519739/12500000000000 : ℝ)*(major2) + (198347738688041/10000000000000 : ℝ)*(sp0) + (495867261869543/25000000000000 : ℝ)*(sp1) + (1983472324134799/100000000000000 : ℝ)*(sp2) + (185771922879883/25000000000000 : ℝ)*(sp3) + (888299309/5000000000000 : ℝ)*(sp5) + (7244664777/50000000000000 : ℝ)*(sp6) + (1074219169/25000000000000 : ℝ)*(sp7) + (4713291971/50000000000000 : ℝ)*(sp8) + (46443249274763/6250000000000 : ℝ)*(f.failure) + (61983962920761/3125000000000 : ℝ)*(f.sum) + (39013788514661/18992500000000000000000000000 : ℝ)*base66 + (1100291840374910077/474812500000000000000000000000000 : ℝ)*base68 + (2731909192809285077/474812500000000000000000000000000 : ℝ)*base70 + (3482694724867785077/474812500000000000000000000000000 : ℝ)*base72 + (317128939651/4748125000000000000000000000 : ℝ)*base73 + (2928809511306785077/474812500000000000000000000000000 : ℝ)*base76 + (5849839758000097577/474812500000000000000000000000000 : ℝ)*base78 + (4242595243409472577/474812500000000000000000000000000 : ℝ)*base80 + (15230546929397/37985000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6797103/625000000000000000000 : ℝ)*base89 + (6797103/625000000000000000000 : ℝ)*base91 + (6797103/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10051/12500 : ℝ) ≤ (381797437918666561505822726117067/474812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11564771/100000000000000 : ℝ)*(upper1) + (7750663/50000000000000 : ℝ)*(upper2) + (12958667/50000000000000 : ℝ)*(upper3) + (87223/160000000000 : ℝ)*(upper4) + (352353364874223/25000000000000 : ℝ)*(major0) + (352353364874223/25000000000000 : ℝ)*(major1) + (352353364874223/25000000000000 : ℝ)*(major2) + (615853163/50000000000000 : ℝ)*(sp0) + (6516618937/50000000000000 : ℝ)*(sp2) + (3689374551/100000000000000 : ℝ)*(sp3) + (1014583835257583/50000000000000 : ℝ)*(sp8) + (507292225555373/25000000000000 : ℝ)*(sp9) + (1014577934491809/50000000000000 : ℝ)*(sp10) + (152570188890807/20000000000000 : ℝ)*(sp11) + (762854633828587/100000000000000 : ℝ)*(f.failure) + (507292225555373/25000000000000 : ℝ)*(f.sum) + (165802756036057/37985000000000000000000000000 : ℝ)*base66 + (1370081841816694311/949625000000000000000000000000000 : ℝ)*base67 + (418625623901319311/949625000000000000000000000000000 : ℝ)*base69 + (3330659801226055689/949625000000000000000000000000000 : ℝ)*base72 + (101641428230353/37985000000000000000000000000 : ℝ)*base73 + (2569013022170819311/949625000000000000000000000000000 : ℝ)*base75 + (6214125543293805689/949625000000000000000000000000000 : ℝ)*base78 + (1814672640146694311/949625000000000000000000000000000 : ℝ)*base79 + (96497310914589/18992500000000000000000000000 : ℝ)*base81 + (114159247/10000000000000000000000 : ℝ)*base89 + (114159247/10000000000000000000000 : ℝ)*base91 + (114159247/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-44983/50000 : ℝ) ≤ (-106789436590627876437333213460563/118703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70870187/100000000000000 : ℝ)*(upper1) + (318297781/100000000000000 : ℝ)*(upper3) + (5920667/25000000000000 : ℝ)*(upper5) + (181920998431253/12500000000000 : ℝ)*(major0) + (181920998431253/12500000000000 : ℝ)*(major1) + (181920998431253/12500000000000 : ℝ)*(major2) + (2116058001/50000000000000 : ℝ)*(sp4) + (22869858841/50000000000000 : ℝ)*(sp5) + (13882737399/50000000000000 : ℝ)*(sp6) + (83109613/200000000000 : ℝ)*(sp7) + (1076495863611711/50000000000000 : ℝ)*(sp12) + (1076475109810871/50000000000000 : ℝ)*(sp13) + (1076484096932313/50000000000000 : ℝ)*(sp14) + (98460785031521/12500000000000 : ℝ)*(sp15) + (196931958764667/25000000000000 : ℝ)*(f.failure) + (67281123729357/3125000000000 : ℝ)*(f.sum) + (4010283422089/9496250000000000000000000000 : ℝ)*base65 + (1560947256102816021/474812500000000000000000000000000 : ℝ)*base67 + (1736845799124933979/474812500000000000000000000000000 : ℝ)*base70 + (256462480295191021/474812500000000000000000000000000 : ℝ)*base71 + (50132124486603/18992500000000000000000000000 : ℝ)*base73 + (11735281534566021/474812500000000000000000000000000 : ℝ)*base75 + (483304658320316021/474812500000000000000000000000000 : ℝ)*base77 + (686518297483441021/474812500000000000000000000000000 : ℝ)*base79 + (109581195621153/18992500000000000000000000000 : ℝ)*base81 + (12010273/2500000000000000000000 : ℝ)*base90 + (12010273/2500000000000000000000 : ℝ)*base92 + (12010273/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1679_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1943/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66489/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57667/100000 : ℝ) else (10051/12500 : ℝ) ≤ X j i ∧ X j i ≤ (44983/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1679_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1679_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66489/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57667/100000 : ℝ) else (10051/12500 : ℝ) ≤ X j i ∧ X j i ≤ (44983/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1679_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1679_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1679_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66489/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57667/100000 : ℝ) else (10051/12500 : ℝ) ≤ X j i ∧ X j i ≤ (44983/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1679_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
