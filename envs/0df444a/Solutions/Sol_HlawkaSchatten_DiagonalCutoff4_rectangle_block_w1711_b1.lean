-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1711_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:40.224903+00:00
-- url     : https://prove2.me/submissions/34d548f5-ed58-4a72-92cd-bf74486feab6

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
theorem support_rectangle_w1711_s3_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1408470181/10000000000 : ℝ)*x 0 + (2734693309/5000000000 : ℝ)*x 1 + (5138421457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1408470181/10000000000 : ℝ)^5311 ≤ (55118338021/625000000000 : ℝ)^4287 := by
    have hnat : (1408470181 : ℕ)^5311*625000000000^4287 ≤ 55118338021^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408470181 10000000000 55118338021 625000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734693309/5000000000 : ℝ)^5311 ≤ (47352422773071/100000000000000 : ℝ)^4287 := by
    have hnat : (2734693309 : ℕ)^5311*100000000000000^4287 ≤ 47352422773071^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734693309 5000000000 47352422773071 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138421457/10000000000 : ℝ)^5311 ≤ (876572862603/2000000000000 : ℝ)^4287 := by
    have hnat : (5138421457 : ℕ)^5311*2000000000000^4287 ≤ 876572862603^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138421457 10000000000 876572862603 2000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1408470181/10000000000 : ℝ), (2734693309/5000000000 : ℝ), (5138421457/10000000000 : ℝ)] ![(55118338021/625000000000 : ℝ), (47352422773071/100000000000000 : ℝ), (876572862603/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1408470181/10000000000 : ℝ)|^5311 ≤ (55118338021/625000000000 : ℝ)^4287
        have hw : |(-1408470181/10000000000 : ℝ)|=(1408470181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734693309/5000000000 : ℝ)|^5311 ≤ (47352422773071/100000000000000 : ℝ)^4287
        have hw : |(2734693309/5000000000 : ℝ)|=(2734693309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138421457/10000000000 : ℝ)|^5311 ≤ (876572862603/2000000000000 : ℝ)^4287
        have hw : |(5138421457/10000000000 : ℝ)|=(5138421457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343181043/10000000000 : ℝ)*x 0 + (-1580070099/10000000000 : ℝ)*x 1 + (5138421489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343181043/10000000000 : ℝ)^5311 ≤ (46002529804989/100000000000000 : ℝ)^4287 := by
    have hnat : (5343181043 : ℕ)^5311*100000000000000^4287 ≤ 46002529804989^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343181043 10000000000 46002529804989 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580070099/10000000000 : ℝ)^5311 ≤ (10168826713847/100000000000000 : ℝ)^4287 := by
    have hnat : (1580070099 : ℕ)^5311*100000000000000^4287 ≤ 10168826713847^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580070099 10000000000 10168826713847 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138421489/10000000000 : ℝ)^5311 ≤ (21914321734147/50000000000000 : ℝ)^4287 := by
    have hnat : (5138421489 : ℕ)^5311*50000000000000^4287 ≤ 21914321734147^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138421489 10000000000 21914321734147 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343181043/10000000000 : ℝ), (-1580070099/10000000000 : ℝ), (5138421489/10000000000 : ℝ)] ![(46002529804989/100000000000000 : ℝ), (10168826713847/100000000000000 : ℝ), (21914321734147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343181043/10000000000 : ℝ)|^5311 ≤ (46002529804989/100000000000000 : ℝ)^4287
        have hw : |(5343181043/10000000000 : ℝ)|=(5343181043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580070099/10000000000 : ℝ)|^5311 ≤ (10168826713847/100000000000000 : ℝ)^4287
        have hw : |(-1580070099/10000000000 : ℝ)|=(1580070099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138421489/10000000000 : ℝ)|^5311 ≤ (21914321734147/50000000000000 : ℝ)^4287
        have hw : |(5138421489/10000000000 : ℝ)|=(5138421489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343181167/10000000000 : ℝ)*x 0 + (5138421391/10000000000 : ℝ)*x 1 + (-1580070063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343181167/10000000000 : ℝ)^5311 ≤ (23001265563791/50000000000000 : ℝ)^4287 := by
    have hnat : (5343181167 : ℕ)^5311*50000000000000^4287 ≤ 23001265563791^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343181167 10000000000 23001265563791 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138421391/10000000000 : ℝ)^5311 ≤ (43828642432729/100000000000000 : ℝ)^4287 := by
    have hnat : (5138421391 : ℕ)^5311*100000000000000^4287 ≤ 43828642432729^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138421391 10000000000 43828642432729 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580070063/10000000000 : ℝ)^5311 ≤ (5084413213411/50000000000000 : ℝ)^4287 := by
    have hnat : (1580070063 : ℕ)^5311*50000000000000^4287 ≤ 5084413213411^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580070063 10000000000 5084413213411 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343181167/10000000000 : ℝ), (5138421391/10000000000 : ℝ), (-1580070063/10000000000 : ℝ)] ![(23001265563791/50000000000000 : ℝ), (43828642432729/100000000000000 : ℝ), (5084413213411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343181167/10000000000 : ℝ)|^5311 ≤ (23001265563791/50000000000000 : ℝ)^4287
        have hw : |(5343181167/10000000000 : ℝ)|=(5343181167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138421391/10000000000 : ℝ)|^5311 ≤ (43828642432729/100000000000000 : ℝ)^4287
        have hw : |(5138421391/10000000000 : ℝ)|=(5138421391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580070063/10000000000 : ℝ)|^5311 ≤ (5084413213411/50000000000000 : ℝ)^4287
        have hw : |(-1580070063/10000000000 : ℝ)|=(1580070063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103425647/10000000000 : ℝ)*x 0 + (364033483/1000000000 : ℝ)*x 1 + (287629303/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103425647/10000000000 : ℝ)^5311 ≤ (16584871628489/50000000000000 : ℝ)^4287 := by
    have hnat : (4103425647 : ℕ)^5311*50000000000000^4287 ≤ 16584871628489^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103425647 10000000000 16584871628489 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364033483/1000000000 : ℝ)^5311 ≤ (1787289202067/6250000000000 : ℝ)^4287 := by
    have hnat : (364033483 : ℕ)^5311*6250000000000^4287 ≤ 1787289202067^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364033483 1000000000 1787289202067 6250000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287629303/625000000 : ℝ)^5311 ≤ (38233629491783/100000000000000 : ℝ)^4287 := by
    have hnat : (287629303 : ℕ)^5311*100000000000000^4287 ≤ 38233629491783^4287*625000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287629303 625000000 38233629491783 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103425647/10000000000 : ℝ), (364033483/1000000000 : ℝ), (287629303/625000000 : ℝ)] ![(16584871628489/50000000000000 : ℝ), (1787289202067/6250000000000 : ℝ), (38233629491783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103425647/10000000000 : ℝ)|^5311 ≤ (16584871628489/50000000000000 : ℝ)^4287
        have hw : |(4103425647/10000000000 : ℝ)|=(4103425647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364033483/1000000000 : ℝ)|^5311 ≤ (1787289202067/6250000000000 : ℝ)^4287
        have hw : |(364033483/1000000000 : ℝ)|=(364033483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287629303/625000000 : ℝ)|^5311 ≤ (38233629491783/100000000000000 : ℝ)^4287
        have hw : |(287629303/625000000 : ℝ)|=(287629303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-704310011/5000000000 : ℝ)*x 0 + (5142089901/10000000000 : ℝ)*x 1 + (1093132697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704310011/5000000000 : ℝ)^5311 ≤ (8820096407983/100000000000000 : ℝ)^4287 := by
    have hnat : (704310011 : ℕ)^5311*100000000000000^4287 ≤ 8820096407983^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704310011 5000000000 8820096407983 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142089901/10000000000 : ℝ)^5311 ≤ (43867410830197/100000000000000 : ℝ)^4287 := by
    have hnat : (5142089901 : ℕ)^5311*100000000000000^4287 ≤ 43867410830197^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142089901 10000000000 43867410830197 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093132697/2000000000 : ℝ)^5311 ≤ (9462498548661/20000000000000 : ℝ)^4287 := by
    have hnat : (1093132697 : ℕ)^5311*20000000000000^4287 ≤ 9462498548661^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093132697 2000000000 9462498548661 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704310011/5000000000 : ℝ), (5142089901/10000000000 : ℝ), (1093132697/2000000000 : ℝ)] ![(8820096407983/100000000000000 : ℝ), (43867410830197/100000000000000 : ℝ), (9462498548661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704310011/5000000000 : ℝ)|^5311 ≤ (8820096407983/100000000000000 : ℝ)^4287
        have hw : |(-704310011/5000000000 : ℝ)|=(704310011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142089901/10000000000 : ℝ)|^5311 ≤ (43867410830197/100000000000000 : ℝ)^4287
        have hw : |(5142089901/10000000000 : ℝ)|=(5142089901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093132697/2000000000 : ℝ)|^5311 ≤ (9462498548661/20000000000000 : ℝ)^4287
        have hw : |(1093132697/2000000000 : ℝ)|=(1093132697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627294437/5000000000 : ℝ)*x 0 + (-1252828081/10000000000 : ℝ)*x 1 + (5465663507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627294437/5000000000 : ℝ)^5311 ≤ (45059478156739/100000000000000 : ℝ)^4287 := by
    have hnat : (2627294437 : ℕ)^5311*100000000000000^4287 ≤ 45059478156739^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627294437 5000000000 45059478156739 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252828081/10000000000 : ℝ)^5311 ≤ (3814014425367/50000000000000 : ℝ)^4287 := by
    have hnat : (1252828081 : ℕ)^5311*50000000000000^4287 ≤ 3814014425367^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252828081 10000000000 3814014425367 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465663507/10000000000 : ℝ)^5311 ≤ (1478515405601/3125000000000 : ℝ)^4287 := by
    have hnat : (5465663507 : ℕ)^5311*3125000000000^4287 ≤ 1478515405601^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465663507 10000000000 1478515405601 3125000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627294437/5000000000 : ℝ), (-1252828081/10000000000 : ℝ), (5465663507/10000000000 : ℝ)] ![(45059478156739/100000000000000 : ℝ), (3814014425367/50000000000000 : ℝ), (1478515405601/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627294437/5000000000 : ℝ)|^5311 ≤ (45059478156739/100000000000000 : ℝ)^4287
        have hw : |(2627294437/5000000000 : ℝ)|=(2627294437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252828081/10000000000 : ℝ)|^5311 ≤ (3814014425367/50000000000000 : ℝ)^4287
        have hw : |(-1252828081/10000000000 : ℝ)|=(1252828081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465663507/10000000000 : ℝ)|^5311 ≤ (1478515405601/3125000000000 : ℝ)^4287
        have hw : |(5465663507/10000000000 : ℝ)|=(5465663507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254588881/10000000000 : ℝ)*x 0 + (2732831759/5000000000 : ℝ)*x 1 + (-156603507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254588881/10000000000 : ℝ)^5311 ≤ (704054347361/1562500000000 : ℝ)^4287 := by
    have hnat : (5254588881 : ℕ)^5311*1562500000000^4287 ≤ 704054347361^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254588881 10000000000 704054347361 1562500000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732831759/5000000000 : ℝ)^5311 ≤ (11828123274299/25000000000000 : ℝ)^4287 := by
    have hnat : (2732831759 : ℕ)^5311*25000000000000^4287 ≤ 11828123274299^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732831759 5000000000 11828123274299 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156603507/1250000000 : ℝ)^5311 ≤ (7628028662159/100000000000000 : ℝ)^4287 := by
    have hnat : (156603507 : ℕ)^5311*100000000000000^4287 ≤ 7628028662159^4287*1250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156603507 1250000000 7628028662159 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254588881/10000000000 : ℝ), (2732831759/5000000000 : ℝ), (-156603507/1250000000 : ℝ)] ![(704054347361/1562500000000 : ℝ), (11828123274299/25000000000000 : ℝ), (7628028662159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254588881/10000000000 : ℝ)|^5311 ≤ (704054347361/1562500000000 : ℝ)^4287
        have hw : |(5254588881/10000000000 : ℝ)|=(5254588881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732831759/5000000000 : ℝ)|^5311 ≤ (11828123274299/25000000000000 : ℝ)^4287
        have hw : |(2732831759/5000000000 : ℝ)|=(2732831759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156603507/1250000000 : ℝ)|^5311 ≤ (7628028662159/100000000000000 : ℝ)^4287
        have hw : |(-156603507/1250000000 : ℝ)|=(156603507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s3_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (410386111/1000000000 : ℝ)*x 0 + (4591408911/10000000000 : ℝ)*x 1 + (3651153653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410386111/1000000000 : ℝ)^5311 ≤ (16587052073447/50000000000000 : ℝ)^4287 := by
    have hnat : (410386111 : ℕ)^5311*50000000000000^4287 ≤ 16587052073447^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410386111 1000000000 16587052073447 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4591408911/10000000000 : ℝ)^5311 ≤ (7624788777093/20000000000000 : ℝ)^4287 := by
    have hnat : (4591408911 : ℕ)^5311*20000000000000^4287 ≤ 7624788777093^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591408911 10000000000 7624788777093 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3651153653/10000000000 : ℝ)^5311 ≤ (5740390391039/20000000000000 : ℝ)^4287 := by
    have hnat : (3651153653 : ℕ)^5311*20000000000000^4287 ≤ 5740390391039^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3651153653 10000000000 5740390391039 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410386111/1000000000 : ℝ), (4591408911/10000000000 : ℝ), (3651153653/10000000000 : ℝ)] ![(16587052073447/50000000000000 : ℝ), (7624788777093/20000000000000 : ℝ), (5740390391039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410386111/1000000000 : ℝ)|^5311 ≤ (16587052073447/50000000000000 : ℝ)^4287
        have hw : |(410386111/1000000000 : ℝ)|=(410386111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4591408911/10000000000 : ℝ)|^5311 ≤ (7624788777093/20000000000000 : ℝ)^4287
        have hw : |(4591408911/10000000000 : ℝ)|=(4591408911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3651153653/10000000000 : ℝ)|^5311 ≤ (5740390391039/20000000000000 : ℝ)^4287
        have hw : |(3651153653/10000000000 : ℝ)|=(3651153653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5009/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8543/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10009/100000 : ℝ) ^ (5303/1024 : ℝ) ≤ (133150353829153/20000000000000000000 : ℝ) := by
    have hpowers : (10009/100000 : ℝ)^5303 ≤ (133150353829153/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10009 : ℕ)^5303*20000000000000000000^1024 ≤ 133150353829153^1024*100000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009 100000 133150353829153 20000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10009/100000 : ℝ)) (X := (133150353829153/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17097/100000 : ℝ) ^ (5303/1024 : ℝ) ≤ (5327015507760751/50000000000000000000 : ℝ) := by
    have hpowers : (17097/100000 : ℝ)^5303 ≤ (5327015507760751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17097 : ℕ)^5303*50000000000000000000^1024 ≤ 5327015507760751^1024*100000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17097 100000 5327015507760751 50000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17097/100000 : ℝ)) (X := (5327015507760751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000133150353829153/10000000000000000000 : ℝ) ≤ (5000012855480849/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (10000133150353829153/10000000000000000000 : ℝ)^1024 ≤ (5000012855480849/5000000000000000 : ℝ)^5303 := by
      have hnat : (10000133150353829153 : ℕ)^1024*5000000000000000^5303 ≤ 5000012855480849^5303*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000133150353829153 10000000000000000000 5000012855480849 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000012855480849/5000000000000000 : ℝ)) (X := (10000133150353829153/10000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011319782784667267/100000000000000000000 : ℝ) ≤ (250005464325961/250000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (100011319782784667267/100000000000000000000 : ℝ)^1024 ≤ (250005464325961/250000000000000 : ℝ)^5303 := by
      have hnat : (100011319782784667267 : ℕ)^1024*250000000000000^5303 ≤ 250005464325961^5303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011319782784667267 100000000000000000000 250005464325961 250000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250005464325961/250000000000000 : ℝ)) (X := (100011319782784667267/100000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005327015507760751/25000000000000000000 : ℝ) ≤ (5000205717557591/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (25005327015507760751/25000000000000000000 : ℝ)^1024 ≤ (5000205717557591/5000000000000000 : ℝ)^5303 := by
      have hnat : (25005327015507760751 : ℕ)^1024*5000000000000000^5303 ≤ 5000205717557591^5303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005327015507760751 25000000000000000000 5000205717557591 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000205717557591/5000000000000000 : ℝ)) (X := (25005327015507760751/25000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(133150353829153/20000000000000000000 : ℝ) ≤ ((17719080381561073517/17720000000000000000 : ℝ)+2*(96431038371/354400000000000 : ℝ)*(10009/100000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (17719080381561073517/17720000000000000000 : ℝ)+2*(96431038371/354400000000000 : ℝ)*(10009/100000 : ℝ)=(5000012855480849/5000000000000000 : ℝ) by norm_num, show 1+2*(133150353829153/20000000000000000000 : ℝ)=(10000133150353829153/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5327015507760751/50000000000000000000 : ℝ)+(133150353829153/20000000000000000000 : ℝ) ≤ ((17719080381561073517/17720000000000000000 : ℝ)+(96431038371/354400000000000 : ℝ)*((17097/100000 : ℝ)+(10009/100000 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (17719080381561073517/17720000000000000000 : ℝ)+(96431038371/354400000000000 : ℝ)*((17097/100000 : ℝ)+(10009/100000 : ℝ))=(250005464325961/250000000000000 : ℝ) by norm_num, show 1+(5327015507760751/50000000000000000000 : ℝ)+(133150353829153/20000000000000000000 : ℝ)=(100011319782784667267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5327015507760751/50000000000000000000 : ℝ) ≤ ((17719080381561073517/17720000000000000000 : ℝ)+2*(96431038371/354400000000000 : ℝ)*(17097/100000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (17719080381561073517/17720000000000000000 : ℝ)+2*(96431038371/354400000000000 : ℝ)*(17097/100000 : ℝ)=(5000205717557591/5000000000000000 : ℝ) by norm_num, show 1+2*(5327015507760751/50000000000000000000 : ℝ)=(25005327015507760751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17719080381561073517/17720000000000000000 : ℝ)*(X 1 0+X 2 0)+(96431038371/354400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10009/100000 : ℝ)) (hi := (17097/100000 : ℝ)) (c := (17719080381561073517/17720000000000000000 : ℝ)) (alpha := (96431038371/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17719080381561073517/17720000000000000000 : ℝ)*(X 0 1+X 2 1)+(96431038371/354400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10009/100000 : ℝ)) (hi := (17097/100000 : ℝ)) (c := (17719080381561073517/17720000000000000000 : ℝ)) (alpha := (96431038371/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17719080381561073517/17720000000000000000 : ℝ)*(X 0 2+X 1 2)+(96431038371/354400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10009/100000 : ℝ)) (hi := (17097/100000 : ℝ)) (c := (17719080381561073517/17720000000000000000 : ℝ)) (alpha := (96431038371/354400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1408470181/10000000000 : ℝ)*X 0 0+(2734693309/5000000000 : ℝ)*X 0 1+(5138421457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343181043/10000000000 : ℝ)*X 1 0+(-1580070099/10000000000 : ℝ)*X 1 1+(5138421489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343181167/10000000000 : ℝ)*X 2 0+(5138421391/10000000000 : ℝ)*X 2 1+(-1580070063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4103425647/10000000000 : ℝ)*X 0 0+(364033483/1000000000 : ℝ)*X 0 1+(287629303/625000000 : ℝ)*X 0 2+(4103425647/10000000000 : ℝ)*X 1 0+(364033483/1000000000 : ℝ)*X 1 1+(287629303/625000000 : ℝ)*X 1 2+(4103425647/10000000000 : ℝ)*X 2 0+(364033483/1000000000 : ℝ)*X 2 1+(287629303/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-704310011/5000000000 : ℝ)*X 0 0+(5142089901/10000000000 : ℝ)*X 0 1+(1093132697/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627294437/5000000000 : ℝ)*X 1 0+(-1252828081/10000000000 : ℝ)*X 1 1+(5465663507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254588881/10000000000 : ℝ)*X 2 0+(2732831759/5000000000 : ℝ)*X 2 1+(-156603507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((410386111/1000000000 : ℝ)*X 0 0+(4591408911/10000000000 : ℝ)*X 0 1+(3651153653/10000000000 : ℝ)*X 0 2+(410386111/1000000000 : ℝ)*X 1 0+(4591408911/10000000000 : ℝ)*X 1 1+(3651153653/10000000000 : ℝ)*X 1 2+(410386111/1000000000 : ℝ)*X 2 0+(4591408911/10000000000 : ℝ)*X 2 1+(3651153653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1087475646255041173603811949/88600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1815483909/100000000000000 : ℝ)*(base19) + (3601497/200000000000 : ℝ)*(base23) + (45340011/100000000000000 : ℝ)*(lower2) + (137577993/50000000000000 : ℝ)*(upper3) + (246583729/100000000000000 : ℝ)*(upper5) + (203065250792501/10000000000000 : ℝ)*(major0) + (203065250792501/10000000000000 : ℝ)*(major1) + (203065250792501/10000000000000 : ℝ)*(major2) + (377685530790311/12500000000000 : ℝ)*(sp0) + (377687661148991/12500000000000 : ℝ)*(sp1) + (377687662990917/12500000000000 : ℝ)*(sp2) + (207958949433827/20000000000000 : ℝ)*(sp3) + (4714588337/25000000000000 : ℝ)*(sp4) + (844358999/12500000000000 : ℝ)*(sp7) + (1039801502041127/100000000000000 : ℝ)*(f.failure) + (755375776168959/25000000000000 : ℝ)*(f.sum) + (388696380461/1772000000000000000000000000 : ℝ)*base66 + (50869409750046017/177200000000000000000000000000000 : ℝ)*base67 + (977781494952446017/177200000000000000000000000000000 : ℝ)*base69 + (344886653580046017/177200000000000000000000000000000 : ℝ)*base71 + (5869902346791/1772000000000000000000000000 : ℝ)*base73 + (653985613938753983/177200000000000000000000000000000 : ℝ)*base76 + (430090495277553983/177200000000000000000000000000000 : ℝ)*base78 + (1150919878513246017/177200000000000000000000000000000 : ℝ)*base79 + (1847971585587/354400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (66631979/10000000000000000000000 : ℝ)*base90 + (66631979/10000000000000000000000 : ℝ)*base92 + (66631979/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5095114716598750772252099751/443000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (795346173/50000000000000 : ℝ)*(base19) + (852805559/50000000000000 : ℝ)*(base23) + (473617081/100000000000000 : ℝ)*(lower1) + (254455393/100000000000000 : ℝ)*(upper3) + (2908601/6250000000000 : ℝ)*(lower4) + (238358631/100000000000000 : ℝ)*(upper5) + (2077003949255799/100000000000000 : ℝ)*(major0) + (2077003949255799/100000000000000 : ℝ)*(major1) + (2077003949255799/100000000000000 : ℝ)*(major2) + (263773621/20000000000000 : ℝ)*(sp2) + (193154476451183/6250000000000 : ℝ)*(sp4) + (1545235016263291/50000000000000 : ℝ)*(sp5) + (618093719747941/20000000000000 : ℝ)*(sp6) + (265883972978267/25000000000000 : ℝ)*(sp7) + (265883972978267/25000000000000 : ℝ)*(f.failure) + (193154476451183/6250000000000 : ℝ)*(f.sum) + (91099473350651/17720000000000000000000000000 : ℝ)*base66 + (34677589548177025083/1772000000000000000000000000000000 : ℝ)*base67 + (2552139633201025083/1772000000000000000000000000000000 : ℝ)*base69 + (157115632312593025083/1772000000000000000000000000000000 : ℝ)*base71 + (33477413298891/17720000000000000000000000000 : ℝ)*base74 + (21487024615833025083/1772000000000000000000000000000000 : ℝ)*base75 + (614960637790974917/1772000000000000000000000000000000 : ℝ)*base78 + (12961073700853025083/1772000000000000000000000000000000 : ℝ)*base79 + (54742785027949/17720000000000000000000000000 : ℝ)*base81 + (15944241/2500000000000000000000 : ℝ)*base89 + (15944241/2500000000000000000000 : ℝ)*base91 + (15944241/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1711_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5009/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8543/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1711_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1711_s4_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-140847517/1000000000 : ℝ)*x 0 + (5469368837/10000000000 : ℝ)*x 1 + (5138435843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140847517/1000000000 : ℝ)^5311 ≤ (8818972782823/100000000000000 : ℝ)^4287 := by
    have hnat : (140847517 : ℕ)^5311*100000000000000^4287 ≤ 8818972782823^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140847517 1000000000 8818972782823 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469368837/10000000000 : ℝ)^5311 ≤ (47352232059143/100000000000000 : ℝ)^4287 := by
    have hnat : (5469368837 : ℕ)^5311*100000000000000^4287 ≤ 47352232059143^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469368837 10000000000 47352232059143 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138435843/10000000000 : ℝ)^5311 ≤ (21914397573429/50000000000000 : ℝ)^4287 := by
    have hnat : (5138435843 : ℕ)^5311*50000000000000^4287 ≤ 21914397573429^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138435843 10000000000 21914397573429 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140847517/1000000000 : ℝ), (5469368837/10000000000 : ℝ), (5138435843/10000000000 : ℝ)] ![(8818972782823/100000000000000 : ℝ), (47352232059143/100000000000000 : ℝ), (21914397573429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140847517/1000000000 : ℝ)|^5311 ≤ (8818972782823/100000000000000 : ℝ)^4287
        have hw : |(-140847517/1000000000 : ℝ)|=(140847517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469368837/10000000000 : ℝ)|^5311 ≤ (47352232059143/100000000000000 : ℝ)^4287
        have hw : |(5469368837/10000000000 : ℝ)|=(5469368837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138435843/10000000000 : ℝ)|^5311 ≤ (21914397573429/50000000000000 : ℝ)^4287
        have hw : |(5138435843/10000000000 : ℝ)|=(5138435843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335793901/2500000000 : ℝ)*x 0 + (-1580056471/10000000000 : ℝ)*x 1 + (5138437261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335793901/2500000000 : ℝ)^5311 ≤ (11500617948053/25000000000000 : ℝ)^4287 := by
    have hnat : (1335793901 : ℕ)^5311*25000000000000^4287 ≤ 11500617948053^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335793901 2500000000 11500617948053 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580056471/10000000000 : ℝ)^5311 ≤ (10168718059029/100000000000000 : ℝ)^4287 := by
    have hnat : (1580056471 : ℕ)^5311*100000000000000^4287 ≤ 10168718059029^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580056471 10000000000 10168718059029 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138437261/10000000000 : ℝ)^5311 ≤ (21914405065427/50000000000000 : ℝ)^4287 := by
    have hnat : (5138437261 : ℕ)^5311*50000000000000^4287 ≤ 21914405065427^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138437261 10000000000 21914405065427 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335793901/2500000000 : ℝ), (-1580056471/10000000000 : ℝ), (5138437261/10000000000 : ℝ)] ![(11500617948053/25000000000000 : ℝ), (10168718059029/100000000000000 : ℝ), (21914405065427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335793901/2500000000 : ℝ)|^5311 ≤ (11500617948053/25000000000000 : ℝ)^4287
        have hw : |(1335793901/2500000000 : ℝ)|=(1335793901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580056471/10000000000 : ℝ)|^5311 ≤ (10168718059029/100000000000000 : ℝ)^4287
        have hw : |(-1580056471/10000000000 : ℝ)|=(1580056471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138437261/10000000000 : ℝ)|^5311 ≤ (21914405065427/50000000000000 : ℝ)^4287
        have hw : |(5138437261/10000000000 : ℝ)|=(5138437261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343176251/10000000000 : ℝ)*x 0 + (5138436129/10000000000 : ℝ)*x 1 + (-790028553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343176251/10000000000 : ℝ)^5311 ≤ (46002478693161/100000000000000 : ℝ)^4287 := by
    have hnat : (5343176251 : ℕ)^5311*100000000000000^4287 ≤ 46002478693161^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343176251 10000000000 46002478693161 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138436129/10000000000 : ℝ)^5311 ≤ (21914399084509/50000000000000 : ℝ)^4287 := by
    have hnat : (5138436129 : ℕ)^5311*50000000000000^4287 ≤ 21914399084509^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138436129 10000000000 21914399084509 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (790028553/5000000000 : ℝ)^5311 ≤ (5084361560911/50000000000000 : ℝ)^4287 := by
    have hnat : (790028553 : ℕ)^5311*50000000000000^4287 ≤ 5084361560911^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790028553 5000000000 5084361560911 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343176251/10000000000 : ℝ), (5138436129/10000000000 : ℝ), (-790028553/5000000000 : ℝ)] ![(46002478693161/100000000000000 : ℝ), (21914399084509/50000000000000 : ℝ), (5084361560911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343176251/10000000000 : ℝ)|^5311 ≤ (46002478693161/100000000000000 : ℝ)^4287
        have hw : |(5343176251/10000000000 : ℝ)|=(5343176251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138436129/10000000000 : ℝ)|^5311 ≤ (21914399084509/50000000000000 : ℝ)^4287
        have hw : |(5138436129/10000000000 : ℝ)|=(5138436129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-790028553/5000000000 : ℝ)|^5311 ≤ (5084361560911/50000000000000 : ℝ)^4287
        have hw : |(-790028553/5000000000 : ℝ)|=(790028553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4103428769/10000000000 : ℝ)*x 0 + (364038159/1000000000 : ℝ)*x 1 + (4602021597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103428769/10000000000 : ℝ)^5311 ≤ (6633954904293/20000000000000 : ℝ)^4287 := by
    have hnat : (4103428769 : ℕ)^5311*20000000000000^4287 ≤ 6633954904293^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103428769 10000000000 6633954904293 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364038159/1000000000 : ℝ)^5311 ≤ (14298541148007/50000000000000 : ℝ)^4287 := by
    have hnat : (364038159 : ℕ)^5311*50000000000000^4287 ≤ 14298541148007^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364038159 1000000000 14298541148007 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4602021597/10000000000 : ℝ)^5311 ≤ (1911657158389/5000000000000 : ℝ)^4287 := by
    have hnat : (4602021597 : ℕ)^5311*5000000000000^4287 ≤ 1911657158389^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602021597 10000000000 1911657158389 5000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103428769/10000000000 : ℝ), (364038159/1000000000 : ℝ), (4602021597/10000000000 : ℝ)] ![(6633954904293/20000000000000 : ℝ), (14298541148007/50000000000000 : ℝ), (1911657158389/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103428769/10000000000 : ℝ)|^5311 ≤ (6633954904293/20000000000000 : ℝ)^4287
        have hw : |(4103428769/10000000000 : ℝ)|=(4103428769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364038159/1000000000 : ℝ)|^5311 ≤ (14298541148007/50000000000000 : ℝ)^4287
        have hw : |(364038159/1000000000 : ℝ)|=(364038159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4602021597/10000000000 : ℝ)|^5311 ≤ (1911657158389/5000000000000 : ℝ)^4287
        have hw : |(4602021597/10000000000 : ℝ)|=(4602021597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1408624629/10000000000 : ℝ)*x 0 + (2571051687/5000000000 : ℝ)*x 1 + (1749007/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1408624629/10000000000 : ℝ)^5311 ≤ (1764026429039/20000000000000 : ℝ)^4287 := by
    have hnat : (1408624629 : ℕ)^5311*20000000000000^4287 ≤ 1764026429039^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408624629 10000000000 1764026429039 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571051687/5000000000 : ℝ)^5311 ≤ (5483444152939/12500000000000 : ℝ)^4287 := by
    have hnat : (2571051687 : ℕ)^5311*12500000000000^4287 ≤ 5483444152939^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571051687 5000000000 5483444152939 12500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749007/3200000 : ℝ)^5311 ≤ (47312314618159/100000000000000 : ℝ)^4287 := by
    have hnat : (1749007 : ℕ)^5311*100000000000000^4287 ≤ 47312314618159^4287*3200000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749007 3200000 47312314618159 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1408624629/10000000000 : ℝ), (2571051687/5000000000 : ℝ), (1749007/3200000 : ℝ)] ![(1764026429039/20000000000000 : ℝ), (5483444152939/12500000000000 : ℝ), (47312314618159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1408624629/10000000000 : ℝ)|^5311 ≤ (1764026429039/20000000000000 : ℝ)^4287
        have hw : |(-1408624629/10000000000 : ℝ)|=(1408624629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571051687/5000000000 : ℝ)|^5311 ≤ (5483444152939/12500000000000 : ℝ)^4287
        have hw : |(2571051687/5000000000 : ℝ)|=(2571051687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1749007/3200000 : ℝ)|^5311 ≤ (47312314618159/100000000000000 : ℝ)^4287
        have hw : |(1749007/3200000 : ℝ)|=(1749007/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328412087/625000000 : ℝ)*x 0 + (-1252847533/10000000000 : ℝ)*x 1 + (5465645349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328412087/625000000 : ℝ)^5311 ≤ (22529763077003/50000000000000 : ℝ)^4287 := by
    have hnat : (328412087 : ℕ)^5311*50000000000000^4287 ≤ 22529763077003^4287*625000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328412087 625000000 22529763077003 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252847533/10000000000 : ℝ)^5311 ≤ (7628175577293/100000000000000 : ℝ)^4287 := by
    have hnat : (1252847533 : ℕ)^5311*100000000000000^4287 ≤ 7628175577293^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252847533 10000000000 7628175577293 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465645349/10000000000 : ℝ)^5311 ≤ (23656149126693/50000000000000 : ℝ)^4287 := by
    have hnat : (5465645349 : ℕ)^5311*50000000000000^4287 ≤ 23656149126693^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465645349 10000000000 23656149126693 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328412087/625000000 : ℝ), (-1252847533/10000000000 : ℝ), (5465645349/10000000000 : ℝ)] ![(22529763077003/50000000000000 : ℝ), (7628175577293/100000000000000 : ℝ), (23656149126693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328412087/625000000 : ℝ)|^5311 ≤ (22529763077003/50000000000000 : ℝ)^4287
        have hw : |(328412087/625000000 : ℝ)|=(328412087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252847533/10000000000 : ℝ)|^5311 ≤ (7628175577293/100000000000000 : ℝ)^4287
        have hw : |(-1252847533/10000000000 : ℝ)|=(1252847533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465645349/10000000000 : ℝ)|^5311 ≤ (23656149126693/50000000000000 : ℝ)^4287
        have hw : |(5465645349/10000000000 : ℝ)|=(5465645349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254593883/10000000000 : ℝ)*x 0 + (2732822711/5000000000 : ℝ)*x 1 + (-1252846737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254593883/10000000000 : ℝ)^5311 ≤ (45059531370177/100000000000000 : ℝ)^4287 := by
    have hnat : (5254593883 : ℕ)^5311*100000000000000^4287 ≤ 45059531370177^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254593883 10000000000 45059531370177 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732822711/5000000000 : ℝ)^5311 ≤ (11828074759059/25000000000000 : ℝ)^4287 := by
    have hnat : (2732822711 : ℕ)^5311*25000000000000^4287 ≤ 11828074759059^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732822711 5000000000 11828074759059 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252846737/10000000000 : ℝ)^5311 ≤ (7628169573049/100000000000000 : ℝ)^4287 := by
    have hnat : (1252846737 : ℕ)^5311*100000000000000^4287 ≤ 7628169573049^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252846737 10000000000 7628169573049 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254593883/10000000000 : ℝ), (2732822711/5000000000 : ℝ), (-1252846737/10000000000 : ℝ)] ![(45059531370177/100000000000000 : ℝ), (11828074759059/25000000000000 : ℝ), (7628169573049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254593883/10000000000 : ℝ)|^5311 ≤ (45059531370177/100000000000000 : ℝ)^4287
        have hw : |(5254593883/10000000000 : ℝ)|=(5254593883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732822711/5000000000 : ℝ)|^5311 ≤ (11828074759059/25000000000000 : ℝ)^4287
        have hw : |(2732822711/5000000000 : ℝ)|=(2732822711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1252846737/10000000000 : ℝ)|^5311 ≤ (7628169573049/100000000000000 : ℝ)^4287
        have hw : |(-1252846737/10000000000 : ℝ)|=(1252846737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_s4_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2051932783/5000000000 : ℝ)*x 0 + (229568087/500000000 : ℝ)*x 1 + (730239779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051932783/5000000000 : ℝ)^5311 ≤ (16587074385761/50000000000000 : ℝ)^4287 := by
    have hnat : (2051932783 : ℕ)^5311*50000000000000^4287 ≤ 16587074385761^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051932783 5000000000 16587074385761 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229568087/500000000 : ℝ)^5311 ≤ (38123458653707/100000000000000 : ℝ)^4287 := by
    have hnat : (229568087 : ℕ)^5311*100000000000000^4287 ≤ 38123458653707^4287*500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229568087 500000000 38123458653707 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730239779/2000000000 : ℝ)^5311 ≤ (112118720927/390625000000 : ℝ)^4287 := by
    have hnat : (730239779 : ℕ)^5311*390625000000^4287 ≤ 112118720927^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730239779 2000000000 112118720927 390625000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2051932783/5000000000 : ℝ), (229568087/500000000 : ℝ), (730239779/2000000000 : ℝ)] ![(16587074385761/50000000000000 : ℝ), (38123458653707/100000000000000 : ℝ), (112118720927/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2051932783/5000000000 : ℝ)|^5311 ≤ (16587074385761/50000000000000 : ℝ)^4287
        have hw : |(2051932783/5000000000 : ℝ)|=(2051932783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229568087/500000000 : ℝ)|^5311 ≤ (38123458653707/100000000000000 : ℝ)^4287
        have hw : |(229568087/500000000 : ℝ)|=(229568087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(730239779/2000000000 : ℝ)|^5311 ≤ (112118720927/390625000000 : ℝ)^4287
        have hw : |(730239779/2000000000 : ℝ)|=(730239779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8543/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5009/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10019/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3417/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8543/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5009/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8543/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5009/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8543/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5009/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8543/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5009/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8543/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5009/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8543/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5009/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5009/50000 : ℝ) ^ (5303/1024 : ℝ) ≤ (668857771298037/100000000000000000000 : ℝ) := by
    have hpowers : (5009/50000 : ℝ)^5303 ≤ (668857771298037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5009 : ℕ)^5303*100000000000000000000^1024 ≤ 668857771298037^1024*50000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5009 50000 668857771298037 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5009/50000 : ℝ)) (X := (668857771298037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8543/50000 : ℝ) ^ (5303/1024 : ℝ) ≤ (10618580333144929/100000000000000000000 : ℝ) := by
    have hpowers : (8543/50000 : ℝ)^5303 ≤ (10618580333144929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8543 : ℕ)^5303*100000000000000000000^1024 ≤ 10618580333144929^1024*50000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8543 50000 10618580333144929 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8543/50000 : ℝ)) (X := (10618580333144929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000668857771298037/50000000000000000000 : ℝ) ≤ (62500161443207/62500000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50000668857771298037/50000000000000000000 : ℝ)^1024 ≤ (62500161443207/62500000000000 : ℝ)^5303 := by
      have hnat : (50000668857771298037 : ℕ)^1024*62500000000000^5303 ≤ 62500161443207^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000668857771298037 50000000000000000000 62500161443207 62500000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500161443207/62500000000000 : ℝ)) (X := (50000668857771298037/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005643719052221483/50000000000000000000 : ℝ) ≤ (5000108974262649/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50005643719052221483/50000000000000000000 : ℝ)^1024 ≤ (5000108974262649/5000000000000000 : ℝ)^5303 := by
      have hnat : (50005643719052221483 : ℕ)^1024*5000000000000000^5303 ≤ 5000108974262649^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005643719052221483 50000000000000000000 5000108974262649 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000108974262649/5000000000000000 : ℝ)) (X := (50005643719052221483/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010618580333144929/50000000000000000000 : ℝ) ≤ (2500102516534369/2500000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50010618580333144929/50000000000000000000 : ℝ)^1024 ≤ (2500102516534369/2500000000000000 : ℝ)^5303 := by
      have hnat : (50010618580333144929 : ℕ)^1024*2500000000000000^5303 ≤ 2500102516534369^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010618580333144929 50000000000000000000 2500102516534369 2500000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500102516534369/2500000000000000 : ℝ)) (X := (50010618580333144929/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(668857771298037/100000000000000000000 : ℝ) ≤ ((8834541663052041719/8835000000000000000 : ℝ)+2*(96058806089/353400000000000 : ℝ)*(5009/50000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (8834541663052041719/8835000000000000000 : ℝ)+2*(96058806089/353400000000000 : ℝ)*(5009/50000 : ℝ)=(62500161443207/62500000000000 : ℝ) by norm_num, show 1+2*(668857771298037/100000000000000000000 : ℝ)=(50000668857771298037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10618580333144929/100000000000000000000 : ℝ)+(668857771298037/100000000000000000000 : ℝ) ≤ ((8834541663052041719/8835000000000000000 : ℝ)+(96058806089/353400000000000 : ℝ)*((8543/50000 : ℝ)+(5009/50000 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (8834541663052041719/8835000000000000000 : ℝ)+(96058806089/353400000000000 : ℝ)*((8543/50000 : ℝ)+(5009/50000 : ℝ))=(5000108974262649/5000000000000000 : ℝ) by norm_num, show 1+(10618580333144929/100000000000000000000 : ℝ)+(668857771298037/100000000000000000000 : ℝ)=(50005643719052221483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10618580333144929/100000000000000000000 : ℝ) ≤ ((8834541663052041719/8835000000000000000 : ℝ)+2*(96058806089/353400000000000 : ℝ)*(8543/50000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (8834541663052041719/8835000000000000000 : ℝ)+2*(96058806089/353400000000000 : ℝ)*(8543/50000 : ℝ)=(2500102516534369/2500000000000000 : ℝ) by norm_num, show 1+2*(10618580333144929/100000000000000000000 : ℝ)=(50010618580333144929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8834541663052041719/8835000000000000000 : ℝ)*(X 1 0+X 2 0)+(96058806089/353400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (5009/50000 : ℝ)) (hi := (8543/50000 : ℝ)) (c := (8834541663052041719/8835000000000000000 : ℝ)) (alpha := (96058806089/353400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8834541663052041719/8835000000000000000 : ℝ)*(X 0 1+X 2 1)+(96058806089/353400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (5009/50000 : ℝ)) (hi := (8543/50000 : ℝ)) (c := (8834541663052041719/8835000000000000000 : ℝ)) (alpha := (96058806089/353400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8834541663052041719/8835000000000000000 : ℝ)*(X 0 2+X 1 2)+(96058806089/353400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (5009/50000 : ℝ)) (hi := (8543/50000 : ℝ)) (c := (8834541663052041719/8835000000000000000 : ℝ)) (alpha := (96058806089/353400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-140847517/1000000000 : ℝ)*X 0 0+(5469368837/10000000000 : ℝ)*X 0 1+(5138435843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335793901/2500000000 : ℝ)*X 1 0+(-1580056471/10000000000 : ℝ)*X 1 1+(5138437261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343176251/10000000000 : ℝ)*X 2 0+(5138436129/10000000000 : ℝ)*X 2 1+(-790028553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4103428769/10000000000 : ℝ)*X 0 0+(364038159/1000000000 : ℝ)*X 0 1+(4602021597/10000000000 : ℝ)*X 0 2+(4103428769/10000000000 : ℝ)*X 1 0+(364038159/1000000000 : ℝ)*X 1 1+(4602021597/10000000000 : ℝ)*X 1 2+(4103428769/10000000000 : ℝ)*X 2 0+(364038159/1000000000 : ℝ)*X 2 1+(4602021597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1408624629/10000000000 : ℝ)*X 0 0+(2571051687/5000000000 : ℝ)*X 0 1+(1749007/3200000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328412087/625000000 : ℝ)*X 1 0+(-1252847533/10000000000 : ℝ)*X 1 1+(5465645349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254593883/10000000000 : ℝ)*X 2 0+(2732822711/5000000000 : ℝ)*X 2 1+(-1252846737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2051932783/5000000000 : ℝ)*X 0 0+(229568087/500000000 : ℝ)*X 0 1+(730239779/2000000000 : ℝ)*X 0 2+(2051932783/5000000000 : ℝ)*X 1 0+(229568087/500000000 : ℝ)*X 1 1+(730239779/2000000000 : ℝ)*X 1 2+(2051932783/5000000000 : ℝ)*X 2 0+(229568087/500000000 : ℝ)*X 2 1+(730239779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23984879717240204048531/5890000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550203501/100000000000000 : ℝ)*(base19) + (928592457/100000000000000 : ℝ)*(base23) + (25172951/100000000000000 : ℝ)*(upper2) + (190333409/100000000000000 : ℝ)*(upper3) + (2030847386048981/100000000000000 : ℝ)*(major0) + (2030847386048981/100000000000000 : ℝ)*(major1) + (2030847386048981/100000000000000 : ℝ)*(major2) + (1510888946666229/50000000000000 : ℝ)*(sp0) + (3021792796207283/100000000000000 : ℝ)*(sp1) + (1510895164510761/50000000000000 : ℝ)*(sp2) + (6499343791571/625000000000 : ℝ)*(sp3) + (7726539163/50000000000000 : ℝ)*(sp4) + (522199201/25000000000000 : ℝ)*(sp6) + (3141648977/50000000000000 : ℝ)*(sp7) + (519950644974657/50000000000000 : ℝ)*(f.failure) + (94431042075337/3125000000000 : ℝ)*(f.sum) + (33617857759009/17670000000000000000000000000 : ℝ)*base65 + (3475618719382836661/883500000000000000000000000000000 : ℝ)*base68 + (928115940673163339/883500000000000000000000000000000 : ℝ)*base69 + (11880034033836661/883500000000000000000000000000000 : ℝ)*base72 + (817353018581/17670000000000000000000000000 : ℝ)*base74 + (6062267275863336661/883500000000000000000000000000000 : ℝ)*base76 + (5912959296529163339/883500000000000000000000000000000 : ℝ)*base77 + (4955165580091163339/883500000000000000000000000000000 : ℝ)*base79 + (66105036612409/17670000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8341789/5000000000000000000000 : ℝ)*base90 + (8341789/5000000000000000000000 : ℝ)*base92 + (8341789/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63491208792809858330379149/36812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (932865819/100000000000000 : ℝ)*(base19) + (1818702879/100000000000000 : ℝ)*(base23) + (33523099/25000000000000 : ℝ)*(lower1) + (113952289/50000000000000 : ℝ)*(lower4) + (37531427/25000000000000 : ℝ)*(upper5) + (519303244056529/25000000000000 : ℝ)*(major0) + (519303244056529/25000000000000 : ℝ)*(major1) + (519303244056529/25000000000000 : ℝ)*(major2) + (5585124349/100000000000000 : ℝ)*(sp0) + (4843482137/50000000000000 : ℝ)*(sp2) + (3090777385058219/100000000000000 : ℝ)*(sp4) + (772695509329187/25000000000000 : ℝ)*(sp5) + (1545385732257707/50000000000000 : ℝ)*(sp6) + (1063642924779033/100000000000000 : ℝ)*(sp7) + (1063642924779033/100000000000000 : ℝ)*(f.failure) + (386347871272821/12500000000000 : ℝ)*(f.sum) + (29729929890667/8835000000000000000000000000 : ℝ)*base65 + (671580608465233351/220875000000000000000000000000000 : ℝ)*base67 + (96442612506766649/220875000000000000000000000000000 : ℝ)*base70 + (451517182282891649/220875000000000000000000000000000 : ℝ)*base72 + (25808317808801/4417500000000000000000000000 : ℝ)*base73 + (2275324574400733351/220875000000000000000000000000000 : ℝ)*base75 + (71042118712108351/220875000000000000000000000000000 : ℝ)*base77 + (2099637532109608351/220875000000000000000000000000000 : ℝ)*base79 + (46387917959707/8835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16263659/10000000000000000000000 : ℝ)*base89 + (16263659/10000000000000000000000 : ℝ)*base91 + (16263659/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1711_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8543/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5009/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1711_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1711_box_0 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090625397/10000000000 : ℝ)*x 0 + (1354174257/2500000000 : ℝ)*x 1 + (5416697493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090625397/10000000000 : ℝ)^5311 ≤ (321205663943/5000000000000 : ℝ)^4287 := by
    have hnat : (1090625397 : ℕ)^5311*5000000000000^4287 ≤ 321205663943^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090625397 10000000000 321205663943 5000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354174257/2500000000 : ℝ)^5311 ≤ (5848492607987/12500000000000 : ℝ)^4287 := by
    have hnat : (1354174257 : ℕ)^5311*12500000000000^4287 ≤ 5848492607987^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354174257 2500000000 5848492607987 12500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416697493/10000000000 : ℝ)^5311 ≤ (46787945839837/100000000000000 : ℝ)^4287 := by
    have hnat : (5416697493 : ℕ)^5311*100000000000000^4287 ≤ 46787945839837^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416697493 10000000000 46787945839837 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090625397/10000000000 : ℝ), (1354174257/2500000000 : ℝ), (5416697493/10000000000 : ℝ)] ![(321205663943/5000000000000 : ℝ), (5848492607987/12500000000000 : ℝ), (46787945839837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090625397/10000000000 : ℝ)|^5311 ≤ (321205663943/5000000000000 : ℝ)^4287
        have hw : |(-1090625397/10000000000 : ℝ)|=(1090625397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354174257/2500000000 : ℝ)|^5311 ≤ (5848492607987/12500000000000 : ℝ)^4287
        have hw : |(1354174257/2500000000 : ℝ)|=(1354174257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416697493/10000000000 : ℝ)|^5311 ≤ (46787945839837/100000000000000 : ℝ)^4287
        have hw : |(5416697493/10000000000 : ℝ)|=(5416697493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_1 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225355153/10000000000 : ℝ)*x 0 + (-1362394729/10000000000 : ℝ)*x 1 + (1083339473/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225355153/10000000000 : ℝ)^5311 ≤ (8949823700347/20000000000000 : ℝ)^4287 := by
    have hnat : (5225355153 : ℕ)^5311*20000000000000^4287 ≤ 8949823700347^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225355153 10000000000 8949823700347 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362394729/10000000000 : ℝ)^5311 ≤ (8462937013043/100000000000000 : ℝ)^4287 := by
    have hnat : (1362394729 : ℕ)^5311*100000000000000^4287 ≤ 8462937013043^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362394729 10000000000 8462937013043 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083339473/2000000000 : ℝ)^5311 ≤ (9357588894023/20000000000000 : ℝ)^4287 := by
    have hnat : (1083339473 : ℕ)^5311*20000000000000^4287 ≤ 9357588894023^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083339473 2000000000 9357588894023 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225355153/10000000000 : ℝ), (-1362394729/10000000000 : ℝ), (1083339473/2000000000 : ℝ)] ![(8949823700347/20000000000000 : ℝ), (8462937013043/100000000000000 : ℝ), (9357588894023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225355153/10000000000 : ℝ)|^5311 ≤ (8949823700347/20000000000000 : ℝ)^4287
        have hw : |(5225355153/10000000000 : ℝ)|=(5225355153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1362394729/10000000000 : ℝ)|^5311 ≤ (8462937013043/100000000000000 : ℝ)^4287
        have hw : |(-1362394729/10000000000 : ℝ)|=(1362394729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083339473/2000000000 : ℝ)|^5311 ≤ (9357588894023/20000000000000 : ℝ)^4287
        have hw : |(1083339473/2000000000 : ℝ)|=(1083339473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_2 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225355147/10000000000 : ℝ)*x 0 + (5416697331/10000000000 : ℝ)*x 1 + (-681197393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225355147/10000000000 : ℝ)^5311 ≤ (44749118438079/100000000000000 : ℝ)^4287 := by
    have hnat : (5225355147 : ℕ)^5311*100000000000000^4287 ≤ 44749118438079^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225355147 10000000000 44749118438079 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416697331/10000000000 : ℝ)^5311 ≤ (46787944106283/100000000000000 : ℝ)^4287 := by
    have hnat : (5416697331 : ℕ)^5311*100000000000000^4287 ≤ 46787944106283^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416697331 10000000000 46787944106283 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681197393/5000000000 : ℝ)^5311 ≤ (8462937451691/100000000000000 : ℝ)^4287 := by
    have hnat : (681197393 : ℕ)^5311*100000000000000^4287 ≤ 8462937451691^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681197393 5000000000 8462937451691 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225355147/10000000000 : ℝ), (5416697331/10000000000 : ℝ), (-681197393/5000000000 : ℝ)] ![(44749118438079/100000000000000 : ℝ), (46787944106283/100000000000000 : ℝ), (8462937451691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225355147/10000000000 : ℝ)|^5311 ≤ (44749118438079/100000000000000 : ℝ)^4287
        have hw : |(5225355147/10000000000 : ℝ)|=(5225355147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416697331/10000000000 : ℝ)|^5311 ≤ (46787944106283/100000000000000 : ℝ)^4287
        have hw : |(5416697331/10000000000 : ℝ)|=(5416697331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-681197393/5000000000 : ℝ)|^5311 ≤ (8462937451691/100000000000000 : ℝ)^4287
        have hw : |(-681197393/5000000000 : ℝ)|=(681197393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_3 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1121294509/2500000000 : ℝ)*x 0 + (983534297/2500000000 : ℝ)*x 1 + (1967068741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121294509/2500000000 : ℝ)^5311 ≤ (37034219774451/100000000000000 : ℝ)^4287 := by
    have hnat : (1121294509 : ℕ)^5311*100000000000000^4287 ≤ 37034219774451^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121294509 2500000000 37034219774451 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983534297/2500000000 : ℝ)^5311 ≤ (31482888644553/100000000000000 : ℝ)^4287 := by
    have hnat : (983534297 : ℕ)^5311*100000000000000^4287 ≤ 31482888644553^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983534297 2500000000 31482888644553 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967068741/5000000000 : ℝ)^5311 ≤ (31482891559263/100000000000000 : ℝ)^4287 := by
    have hnat : (1967068741 : ℕ)^5311*100000000000000^4287 ≤ 31482891559263^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967068741 5000000000 31482891559263 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121294509/2500000000 : ℝ), (983534297/2500000000 : ℝ), (1967068741/5000000000 : ℝ)] ![(37034219774451/100000000000000 : ℝ), (31482888644553/100000000000000 : ℝ), (31482891559263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121294509/2500000000 : ℝ)|^5311 ≤ (37034219774451/100000000000000 : ℝ)^4287
        have hw : |(1121294509/2500000000 : ℝ)|=(1121294509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983534297/2500000000 : ℝ)|^5311 ≤ (31482888644553/100000000000000 : ℝ)^4287
        have hw : |(983534297/2500000000 : ℝ)|=(983534297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1967068741/5000000000 : ℝ)|^5311 ≤ (31482891559263/100000000000000 : ℝ)^4287
        have hw : |(1967068741/5000000000 : ℝ)|=(1967068741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_4 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69877607/400000000 : ℝ)*x 0 + (5177521797/10000000000 : ℝ)*x 1 + (2588760877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69877607/400000000 : ℝ)^5311 ≤ (719726198727/6250000000000 : ℝ)^4287 := by
    have hnat : (69877607 : ℕ)^5311*6250000000000^4287 ≤ 719726198727^4287*400000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69877607 400000000 719726198727 6250000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177521797/10000000000 : ℝ)^5311 ≤ (4424219063313/10000000000000 : ℝ)^4287 := by
    have hnat : (5177521797 : ℕ)^5311*10000000000000^4287 ≤ 4424219063313^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177521797 10000000000 4424219063313 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588760877/5000000000 : ℝ)^5311 ≤ (22121095088963/50000000000000 : ℝ)^4287 := by
    have hnat : (2588760877 : ℕ)^5311*50000000000000^4287 ≤ 22121095088963^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588760877 5000000000 22121095088963 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69877607/400000000 : ℝ), (5177521797/10000000000 : ℝ), (2588760877/5000000000 : ℝ)] ![(719726198727/6250000000000 : ℝ), (4424219063313/10000000000000 : ℝ), (22121095088963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69877607/400000000 : ℝ)|^5311 ≤ (719726198727/6250000000000 : ℝ)^4287
        have hw : |(-69877607/400000000 : ℝ)|=(69877607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177521797/10000000000 : ℝ)|^5311 ≤ (4424219063313/10000000000000 : ℝ)^4287
        have hw : |(5177521797/10000000000 : ℝ)|=(5177521797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588760877/5000000000 : ℝ)|^5311 ≤ (22121095088963/50000000000000 : ℝ)^4287
        have hw : |(2588760877/5000000000 : ℝ)|=(2588760877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_5 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693759909/5000000000 : ℝ)*x 0 + (-1467857183/10000000000 : ℝ)*x 1 + (5177521737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693759909/5000000000 : ℝ)^5311 ≤ (9295183645191/20000000000000 : ℝ)^4287 := by
    have hnat : (2693759909 : ℕ)^5311*20000000000000^4287 ≤ 9295183645191^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693759909 5000000000 9295183645191 20000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1467857183/10000000000 : ℝ)^5311 ≤ (2320472940893/25000000000000 : ℝ)^4287 := by
    have hnat : (1467857183 : ℕ)^5311*25000000000000^4287 ≤ 2320472940893^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467857183 10000000000 2320472940893 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177521737/10000000000 : ℝ)^5311 ≤ (44242189997961/100000000000000 : ℝ)^4287 := by
    have hnat : (5177521737 : ℕ)^5311*100000000000000^4287 ≤ 44242189997961^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177521737 10000000000 44242189997961 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693759909/5000000000 : ℝ), (-1467857183/10000000000 : ℝ), (5177521737/10000000000 : ℝ)] ![(9295183645191/20000000000000 : ℝ), (2320472940893/25000000000000 : ℝ), (44242189997961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693759909/5000000000 : ℝ)|^5311 ≤ (9295183645191/20000000000000 : ℝ)^4287
        have hw : |(2693759909/5000000000 : ℝ)|=(2693759909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1467857183/10000000000 : ℝ)|^5311 ≤ (2320472940893/25000000000000 : ℝ)^4287
        have hw : |(-1467857183/10000000000 : ℝ)|=(1467857183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177521737/10000000000 : ℝ)|^5311 ≤ (44242189997961/100000000000000 : ℝ)^4287
        have hw : |(5177521737/10000000000 : ℝ)|=(5177521737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_6 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077503951/2000000000 : ℝ)*x 0 + (2588760907/5000000000 : ℝ)*x 1 + (-293571433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077503951/2000000000 : ℝ)^5311 ≤ (5809489694083/12500000000000 : ℝ)^4287 := by
    have hnat : (1077503951 : ℕ)^5311*12500000000000^4287 ≤ 5809489694083^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077503951 2000000000 5809489694083 12500000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588760907/5000000000 : ℝ)^5311 ≤ (22121095406547/50000000000000 : ℝ)^4287 := by
    have hnat : (2588760907 : ℕ)^5311*50000000000000^4287 ≤ 22121095406547^4287*5000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588760907 5000000000 22121095406547 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293571433/2000000000 : ℝ)^5311 ≤ (4640945811281/50000000000000 : ℝ)^4287 := by
    have hnat : (293571433 : ℕ)^5311*50000000000000^4287 ≤ 4640945811281^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293571433 2000000000 4640945811281 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077503951/2000000000 : ℝ), (2588760907/5000000000 : ℝ), (-293571433/2000000000 : ℝ)] ![(5809489694083/12500000000000 : ℝ), (22121095406547/50000000000000 : ℝ), (4640945811281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077503951/2000000000 : ℝ)|^5311 ≤ (5809489694083/12500000000000 : ℝ)^4287
        have hw : |(1077503951/2000000000 : ℝ)|=(1077503951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588760907/5000000000 : ℝ)|^5311 ≤ (22121095406547/50000000000000 : ℝ)^4287
        have hw : |(2588760907/5000000000 : ℝ)|=(2588760907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293571433/2000000000 : ℝ)|^5311 ≤ (4640945811281/50000000000000 : ℝ)^4287
        have hw : |(-293571433/2000000000 : ℝ)|=(293571433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_7 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (463247067/1250000000 : ℝ)*x 0 + (432291243/1000000000 : ℝ)*x 1 + (4322912411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463247067/1250000000 : ℝ)^5311 ≤ (29236813265027/100000000000000 : ℝ)^4287 := by
    have hnat : (463247067 : ℕ)^5311*100000000000000^4287 ≤ 29236813265027^4287*1250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463247067 1250000000 29236813265027 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432291243/1000000000 : ℝ)^5311 ≤ (35381593455251/100000000000000 : ℝ)^4287 := by
    have hnat : (432291243 : ℕ)^5311*100000000000000^4287 ≤ 35381593455251^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432291243 1000000000 35381593455251 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4322912411/10000000000 : ℝ)^5311 ≤ (17690796631299/50000000000000 : ℝ)^4287 := by
    have hnat : (4322912411 : ℕ)^5311*50000000000000^4287 ≤ 17690796631299^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322912411 10000000000 17690796631299 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463247067/1250000000 : ℝ), (432291243/1000000000 : ℝ), (4322912411/10000000000 : ℝ)] ![(29236813265027/100000000000000 : ℝ), (35381593455251/100000000000000 : ℝ), (17690796631299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463247067/1250000000 : ℝ)|^5311 ≤ (29236813265027/100000000000000 : ℝ)^4287
        have hw : |(463247067/1250000000 : ℝ)|=(463247067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432291243/1000000000 : ℝ)|^5311 ≤ (35381593455251/100000000000000 : ℝ)^4287
        have hw : |(432291243/1000000000 : ℝ)|=(432291243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4322912411/10000000000 : ℝ)|^5311 ≤ (17690796631299/50000000000000 : ℝ)^4287
        have hw : |(4322912411/10000000000 : ℝ)|=(4322912411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_8 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1605766079/10000000000 : ℝ)*x 0 + (5000942397/10000000000 : ℝ)*x 1 + (5459399509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605766079/10000000000 : ℝ)^5311 ≤ (10374094943733/100000000000000 : ℝ)^4287 := by
    have hnat : (1605766079 : ℕ)^5311*100000000000000^4287 ≤ 10374094943733^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605766079 10000000000 10374094943733 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5000942397/10000000000 : ℝ)^5311 ≤ (21190288907237/50000000000000 : ℝ)^4287 := by
    have hnat : (5000942397 : ℕ)^5311*50000000000000^4287 ≤ 21190288907237^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000942397 10000000000 21190288907237 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459399509/10000000000 : ℝ)^5311 ≤ (11811331805931/25000000000000 : ℝ)^4287 := by
    have hnat : (5459399509 : ℕ)^5311*25000000000000^4287 ≤ 11811331805931^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459399509 10000000000 11811331805931 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1605766079/10000000000 : ℝ), (5000942397/10000000000 : ℝ), (5459399509/10000000000 : ℝ)] ![(10374094943733/100000000000000 : ℝ), (21190288907237/50000000000000 : ℝ), (11811331805931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1605766079/10000000000 : ℝ)|^5311 ≤ (10374094943733/100000000000000 : ℝ)^4287
        have hw : |(-1605766079/10000000000 : ℝ)|=(1605766079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5000942397/10000000000 : ℝ)|^5311 ≤ (21190288907237/50000000000000 : ℝ)^4287
        have hw : |(5000942397/10000000000 : ℝ)|=(5000942397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459399509/10000000000 : ℝ)|^5311 ≤ (11811331805931/25000000000000 : ℝ)^4287
        have hw : |(5459399509/10000000000 : ℝ)|=(5459399509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_9 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299105489/2500000000 : ℝ)*x 0 + (-53711539/400000000 : ℝ)*x 1 + (1364849863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299105489/2500000000 : ℝ)^5311 ≤ (44442357451909/100000000000000 : ℝ)^4287 := by
    have hnat : (1299105489 : ℕ)^5311*100000000000000^4287 ≤ 44442357451909^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299105489 2500000000 44442357451909 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53711539/400000000 : ℝ)^5311 ≤ (2078078982081/25000000000000 : ℝ)^4287 := by
    have hnat : (53711539 : ℕ)^5311*25000000000000^4287 ≤ 2078078982081^4287*400000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53711539 400000000 2078078982081 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364849863/2500000000 : ℝ)^5311 ≤ (2952832913289/6250000000000 : ℝ)^4287 := by
    have hnat : (1364849863 : ℕ)^5311*6250000000000^4287 ≤ 2952832913289^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364849863 2500000000 2952832913289 6250000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299105489/2500000000 : ℝ), (-53711539/400000000 : ℝ), (1364849863/2500000000 : ℝ)] ![(44442357451909/100000000000000 : ℝ), (2078078982081/25000000000000 : ℝ), (2952832913289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299105489/2500000000 : ℝ)|^5311 ≤ (44442357451909/100000000000000 : ℝ)^4287
        have hw : |(1299105489/2500000000 : ℝ)|=(1299105489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53711539/400000000 : ℝ)|^5311 ≤ (2078078982081/25000000000000 : ℝ)^4287
        have hw : |(-53711539/400000000 : ℝ)|=(53711539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364849863/2500000000 : ℝ)|^5311 ≤ (2952832913289/6250000000000 : ℝ)^4287
        have hw : |(1364849863/2500000000 : ℝ)|=(1364849863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_10 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299105393/2500000000 : ℝ)*x 0 + (5459399787/10000000000 : ℝ)*x 1 + (-167848567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299105393/2500000000 : ℝ)^5311 ≤ (11110588345823/25000000000000 : ℝ)^4287 := by
    have hnat : (1299105393 : ℕ)^5311*25000000000000^4287 ≤ 11110588345823^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299105393 2500000000 11110588345823 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459399787/10000000000 : ℝ)^5311 ≤ (11811332551043/25000000000000 : ℝ)^4287 := by
    have hnat : (5459399787 : ℕ)^5311*25000000000000^4287 ≤ 11811332551043^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459399787 10000000000 11811332551043 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167848567/1250000000 : ℝ)^5311 ≤ (8312316396131/100000000000000 : ℝ)^4287 := by
    have hnat : (167848567 : ℕ)^5311*100000000000000^4287 ≤ 8312316396131^4287*1250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167848567 1250000000 8312316396131 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299105393/2500000000 : ℝ), (5459399787/10000000000 : ℝ), (-167848567/1250000000 : ℝ)] ![(11110588345823/25000000000000 : ℝ), (11811332551043/25000000000000 : ℝ), (8312316396131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299105393/2500000000 : ℝ)|^5311 ≤ (11110588345823/25000000000000 : ℝ)^4287
        have hw : |(1299105393/2500000000 : ℝ)|=(1299105393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459399787/10000000000 : ℝ)|^5311 ≤ (11811332551043/25000000000000 : ℝ)^4287
        have hw : |(5459399787/10000000000 : ℝ)|=(5459399787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167848567/1250000000 : ℝ)|^5311 ≤ (8312316396131/100000000000000 : ℝ)^4287
        have hw : |(-167848567/1250000000 : ℝ)|=(167848567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_11 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4619313149/10000000000 : ℝ)*x 0 + (30916349/80000000 : ℝ)*x 1 + (772908697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4619313149/10000000000 : ℝ)^5311 ≤ (38411193505971/100000000000000 : ℝ)^4287 := by
    have hnat : (4619313149 : ℕ)^5311*100000000000000^4287 ≤ 38411193505971^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619313149 10000000000 38411193505971 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30916349/80000000 : ℝ)^5311 ≤ (3079440392983/10000000000000 : ℝ)^4287 := by
    have hnat : (30916349 : ℕ)^5311*10000000000000^4287 ≤ 3079440392983^4287*80000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30916349 80000000 3079440392983 10000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (772908697/2000000000 : ℝ)^5311 ≤ (15397201273889/50000000000000 : ℝ)^4287 := by
    have hnat : (772908697 : ℕ)^5311*50000000000000^4287 ≤ 15397201273889^4287*2000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772908697 2000000000 15397201273889 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4619313149/10000000000 : ℝ), (30916349/80000000 : ℝ), (772908697/2000000000 : ℝ)] ![(38411193505971/100000000000000 : ℝ), (3079440392983/10000000000000 : ℝ), (15397201273889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4619313149/10000000000 : ℝ)|^5311 ≤ (38411193505971/100000000000000 : ℝ)^4287
        have hw : |(4619313149/10000000000 : ℝ)|=(4619313149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30916349/80000000 : ℝ)|^5311 ≤ (3079440392983/10000000000000 : ℝ)^4287
        have hw : |(30916349/80000000 : ℝ)|=(30916349/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(772908697/2000000000 : ℝ)|^5311 ≤ (15397201273889/50000000000000 : ℝ)^4287
        have hw : |(772908697/2000000000 : ℝ)|=(772908697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_12 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1226316791/10000000000 : ℝ)*x 0 + (5584940129/10000000000 : ℝ)*x 1 + (1288102539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1226316791/10000000000 : ℝ)^5311 ≤ (7428562527099/100000000000000 : ℝ)^4287 := by
    have hnat : (1226316791 : ℕ)^5311*100000000000000^4287 ≤ 7428562527099^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226316791 10000000000 7428562527099 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5584940129/10000000000 : ℝ)^5311 ≤ (48594927913509/100000000000000 : ℝ)^4287 := by
    have hnat : (5584940129 : ℕ)^5311*100000000000000^4287 ≤ 48594927913509^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5584940129 10000000000 48594927913509 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288102539/2500000000 : ℝ)^5311 ≤ (2198825477037/5000000000000 : ℝ)^4287 := by
    have hnat : (1288102539 : ℕ)^5311*5000000000000^4287 ≤ 2198825477037^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288102539 2500000000 2198825477037 5000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1226316791/10000000000 : ℝ), (5584940129/10000000000 : ℝ), (1288102539/2500000000 : ℝ)] ![(7428562527099/100000000000000 : ℝ), (48594927913509/100000000000000 : ℝ), (2198825477037/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1226316791/10000000000 : ℝ)|^5311 ≤ (7428562527099/100000000000000 : ℝ)^4287
        have hw : |(-1226316791/10000000000 : ℝ)|=(1226316791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5584940129/10000000000 : ℝ)|^5311 ≤ (48594927913509/100000000000000 : ℝ)^4287
        have hw : |(5584940129/10000000000 : ℝ)|=(5584940129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1288102539/2500000000 : ℝ)|^5311 ≤ (2198825477037/5000000000000 : ℝ)^4287
        have hw : |(1288102539/2500000000 : ℝ)|=(1288102539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_13 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404576917/10000000000 : ℝ)*x 0 + (-1478484233/10000000000 : ℝ)*x 1 + (515240989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404576917/10000000000 : ℝ)^5311 ≤ (23329139439779/50000000000000 : ℝ)^4287 := by
    have hnat : (5404576917 : ℕ)^5311*50000000000000^4287 ≤ 23329139439779^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404576917 10000000000 23329139439779 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1478484233/10000000000 : ℝ)^5311 ≤ (4682607190789/50000000000000 : ℝ)^4287 := by
    have hnat : (1478484233 : ℕ)^5311*50000000000000^4287 ≤ 4682607190789^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478484233 10000000000 4682607190789 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515240989/1000000000 : ℝ)^5311 ≤ (1374265835253/3125000000000 : ℝ)^4287 := by
    have hnat : (515240989 : ℕ)^5311*3125000000000^4287 ≤ 1374265835253^4287*1000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515240989 1000000000 1374265835253 3125000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404576917/10000000000 : ℝ), (-1478484233/10000000000 : ℝ), (515240989/1000000000 : ℝ)] ![(23329139439779/50000000000000 : ℝ), (4682607190789/50000000000000 : ℝ), (1374265835253/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404576917/10000000000 : ℝ)|^5311 ≤ (23329139439779/50000000000000 : ℝ)^4287
        have hw : |(5404576917/10000000000 : ℝ)|=(5404576917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1478484233/10000000000 : ℝ)|^5311 ≤ (4682607190789/50000000000000 : ℝ)^4287
        have hw : |(-1478484233/10000000000 : ℝ)|=(1478484233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515240989/1000000000 : ℝ)|^5311 ≤ (1374265835253/3125000000000 : ℝ)^4287
        have hw : |(515240989/1000000000 : ℝ)|=(515240989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_14 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84446513/156250000 : ℝ)*x 0 + (5152409727/10000000000 : ℝ)*x 1 + (-184810571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84446513/156250000 : ℝ)^5311 ≤ (1458071186577/3125000000000 : ℝ)^4287 := by
    have hnat : (84446513 : ℕ)^5311*3125000000000^4287 ≤ 1458071186577^4287*156250000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84446513 156250000 1458071186577 3125000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152409727/10000000000 : ℝ)^5311 ≤ (43976505004559/100000000000000 : ℝ)^4287 := by
    have hnat : (5152409727 : ℕ)^5311*100000000000000^4287 ≤ 43976505004559^4287*10000000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152409727 10000000000 43976505004559 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184810571/1250000000 : ℝ)^5311 ≤ (4682608505223/50000000000000 : ℝ)^4287 := by
    have hnat : (184810571 : ℕ)^5311*50000000000000^4287 ≤ 4682608505223^4287*1250000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184810571 1250000000 4682608505223 50000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84446513/156250000 : ℝ), (5152409727/10000000000 : ℝ), (-184810571/1250000000 : ℝ)] ![(1458071186577/3125000000000 : ℝ), (43976505004559/100000000000000 : ℝ), (4682608505223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84446513/156250000 : ℝ)|^5311 ≤ (1458071186577/3125000000000 : ℝ)^4287
        have hw : |(84446513/156250000 : ℝ)|=(84446513/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152409727/10000000000 : ℝ)|^5311 ≤ (43976505004559/100000000000000 : ℝ)^4287
        have hw : |(5152409727/10000000000 : ℝ)|=(5152409727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184810571/1250000000 : ℝ)|^5311 ≤ (4682608505223/50000000000000 : ℝ)^4287
        have hw : |(-184810571/1250000000 : ℝ)|=(184810571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1711_box_15 (p : ℝ) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (72423631/200000000 : ℝ)*x 0 + (272726313/625000000 : ℝ)*x 1 + (1090905167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72423631/200000000 : ℝ)^5311 ≤ (7102586821243/25000000000000 : ℝ)^4287 := by
    have hnat : (72423631 : ℕ)^5311*25000000000000^4287 ≤ 7102586821243^4287*200000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72423631 200000000 7102586821243 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272726313/625000000 : ℝ)^5311 ≤ (8948707020001/25000000000000 : ℝ)^4287 := by
    have hnat : (272726313 : ℕ)^5311*25000000000000^4287 ≤ 8948707020001^4287*625000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272726313 625000000 8948707020001 25000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090905167/2500000000 : ℝ)^5311 ≤ (35794824624789/100000000000000 : ℝ)^4287 := by
    have hnat : (1090905167 : ℕ)^5311*100000000000000^4287 ≤ 35794824624789^4287*2500000000^5311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090905167 2500000000 35794824624789 100000000000000 5311 4287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5311/1024 : ℝ)) 5311 4287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(72423631/200000000 : ℝ), (272726313/625000000 : ℝ), (1090905167/2500000000 : ℝ)] ![(7102586821243/25000000000000 : ℝ), (8948707020001/25000000000000 : ℝ), (35794824624789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(72423631/200000000 : ℝ)|^5311 ≤ (7102586821243/25000000000000 : ℝ)^4287
        have hw : |(72423631/200000000 : ℝ)|=(72423631/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272726313/625000000 : ℝ)|^5311 ≤ (8948707020001/25000000000000 : ℝ)^4287
        have hw : |(272726313/625000000 : ℝ)|=(272726313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090905167/2500000000 : ℝ)|^5311 ≤ (35794824624789/100000000000000 : ℝ)^4287
        have hw : |(1090905167/2500000000 : ℝ)|=(1090905167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1711_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16689/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29213/50000 : ℝ) ∧ (40757/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90437/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3417/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3417/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3417/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3417/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3417/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3417/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10019/100000 : ℝ) ^ (5303/1024 : ℝ) ≤ (669203603155421/100000000000000000000 : ℝ) := by
    have hpowers : (10019/100000 : ℝ)^5303 ≤ (669203603155421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10019 : ℕ)^5303*100000000000000000000^1024 ≤ 669203603155421^1024*100000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10019 100000 669203603155421 100000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10019/100000 : ℝ)) (X := (669203603155421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3417/20000 : ℝ) ^ (5303/1024 : ℝ) ≤ (5307681134791239/50000000000000000000 : ℝ) := by
    have hpowers : (3417/20000 : ℝ)^5303 ≤ (5307681134791239/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3417 : ℕ)^5303*50000000000000000000^1024 ≤ 5307681134791239^1024*20000^5303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3417 20000 5307681134791239 50000000000000000000 5303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3417/20000 : ℝ)) (X := (5307681134791239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000669203603155421/50000000000000000000 : ℝ) ≤ (10000025844268881/10000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (50000669203603155421/50000000000000000000 : ℝ)^1024 ≤ (10000025844268881/10000000000000000 : ℝ)^5303 := by
      have hnat : (50000669203603155421 : ℕ)^1024*10000000000000000^5303 ≤ 10000025844268881^5303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000669203603155421 50000000000000000000 10000025844268881 10000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000025844268881/10000000000000000 : ℝ)) (X := (50000669203603155421/50000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011284565872737899/100000000000000000000 : ℝ) ≤ (5000108946534029/5000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (100011284565872737899/100000000000000000000 : ℝ)^1024 ≤ (5000108946534029/5000000000000000 : ℝ)^5303 := by
      have hnat : (100011284565872737899 : ℕ)^1024*5000000000000000^5303 ≤ 5000108946534029^5303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011284565872737899 100000000000000000000 5000108946534029 5000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000108946534029/5000000000000000 : ℝ)) (X := (100011284565872737899/100000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005307681134791239/25000000000000000000 : ℝ) ≤ (2000081988373447/2000000000000000 : ℝ) ^ (5303/1024 : ℝ) := by
    have hpowers : (25005307681134791239/25000000000000000000 : ℝ)^1024 ≤ (2000081988373447/2000000000000000 : ℝ)^5303 := by
      have hnat : (25005307681134791239 : ℕ)^1024*2000000000000000^5303 ≤ 2000081988373447^5303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005307681134791239 25000000000000000000 2000081988373447 2000000000000000 1024 5303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081988373447/2000000000000000 : ℝ)) (X := (25005307681134791239/25000000000000000000 : ℝ)) (by norm_num) 5303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(669203603155421/100000000000000000000 : ℝ) ≤ ((3532816717088300221/3533000000000000000 : ℝ)+2*(192048799177/706600000000000 : ℝ)*(10019/100000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (3532816717088300221/3533000000000000000 : ℝ)+2*(192048799177/706600000000000 : ℝ)*(10019/100000 : ℝ)=(10000025844268881/10000000000000000 : ℝ) by norm_num, show 1+2*(669203603155421/100000000000000000000 : ℝ)=(50000669203603155421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5307681134791239/50000000000000000000 : ℝ)+(669203603155421/100000000000000000000 : ℝ) ≤ ((3532816717088300221/3533000000000000000 : ℝ)+(192048799177/706600000000000 : ℝ)*((3417/20000 : ℝ)+(10019/100000 : ℝ)))^(5303/1024 : ℝ) := by
    rw [show (3532816717088300221/3533000000000000000 : ℝ)+(192048799177/706600000000000 : ℝ)*((3417/20000 : ℝ)+(10019/100000 : ℝ))=(5000108946534029/5000000000000000 : ℝ) by norm_num, show 1+(5307681134791239/50000000000000000000 : ℝ)+(669203603155421/100000000000000000000 : ℝ)=(100011284565872737899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5307681134791239/50000000000000000000 : ℝ) ≤ ((3532816717088300221/3533000000000000000 : ℝ)+2*(192048799177/706600000000000 : ℝ)*(3417/20000 : ℝ))^(5303/1024 : ℝ) := by
    rw [show (3532816717088300221/3533000000000000000 : ℝ)+2*(192048799177/706600000000000 : ℝ)*(3417/20000 : ℝ)=(2000081988373447/2000000000000000 : ℝ) by norm_num, show 1+2*(5307681134791239/50000000000000000000 : ℝ)=(25005307681134791239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3532816717088300221/3533000000000000000 : ℝ)*(X 1 0+X 2 0)+(192048799177/706600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10019/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (3532816717088300221/3533000000000000000 : ℝ)) (alpha := (192048799177/706600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3532816717088300221/3533000000000000000 : ℝ)*(X 0 1+X 2 1)+(192048799177/706600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10019/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (3532816717088300221/3533000000000000000 : ℝ)) (alpha := (192048799177/706600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3532816717088300221/3533000000000000000 : ℝ)*(X 0 2+X 1 2)+(192048799177/706600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5303/1024 : ℝ)) (lo := (10019/100000 : ℝ)) (hi := (3417/20000 : ℝ)) (c := (3532816717088300221/3533000000000000000 : ℝ)) (alpha := (192048799177/706600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090625397/10000000000 : ℝ)*X 0 0+(1354174257/2500000000 : ℝ)*X 0 1+(5416697493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225355153/10000000000 : ℝ)*X 1 0+(-1362394729/10000000000 : ℝ)*X 1 1+(1083339473/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225355147/10000000000 : ℝ)*X 2 0+(5416697331/10000000000 : ℝ)*X 2 1+(-681197393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1121294509/2500000000 : ℝ)*X 0 0+(983534297/2500000000 : ℝ)*X 0 1+(1967068741/5000000000 : ℝ)*X 0 2+(1121294509/2500000000 : ℝ)*X 1 0+(983534297/2500000000 : ℝ)*X 1 1+(1967068741/5000000000 : ℝ)*X 1 2+(1121294509/2500000000 : ℝ)*X 2 0+(983534297/2500000000 : ℝ)*X 2 1+(1967068741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69877607/400000000 : ℝ)*X 0 0+(5177521797/10000000000 : ℝ)*X 0 1+(2588760877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2693759909/5000000000 : ℝ)*X 1 0+(-1467857183/10000000000 : ℝ)*X 1 1+(5177521737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1077503951/2000000000 : ℝ)*X 2 0+(2588760907/5000000000 : ℝ)*X 2 1+(-293571433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((463247067/1250000000 : ℝ)*X 0 0+(432291243/1000000000 : ℝ)*X 0 1+(4322912411/10000000000 : ℝ)*X 0 2+(463247067/1250000000 : ℝ)*X 1 0+(432291243/1000000000 : ℝ)*X 1 1+(4322912411/10000000000 : ℝ)*X 1 2+(463247067/1250000000 : ℝ)*X 2 0+(432291243/1000000000 : ℝ)*X 2 1+(4322912411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1605766079/10000000000 : ℝ)*X 0 0+(5000942397/10000000000 : ℝ)*X 0 1+(5459399509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1299105489/2500000000 : ℝ)*X 1 0+(-53711539/400000000 : ℝ)*X 1 1+(1364849863/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299105393/2500000000 : ℝ)*X 2 0+(5459399787/10000000000 : ℝ)*X 2 1+(-167848567/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4619313149/10000000000 : ℝ)*X 0 0+(30916349/80000000 : ℝ)*X 0 1+(772908697/2000000000 : ℝ)*X 0 2+(4619313149/10000000000 : ℝ)*X 1 0+(30916349/80000000 : ℝ)*X 1 1+(772908697/2000000000 : ℝ)*X 1 2+(4619313149/10000000000 : ℝ)*X 2 0+(30916349/80000000 : ℝ)*X 2 1+(772908697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1226316791/10000000000 : ℝ)*X 0 0+(5584940129/10000000000 : ℝ)*X 0 1+(1288102539/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5404576917/10000000000 : ℝ)*X 1 0+(-1478484233/10000000000 : ℝ)*X 1 1+(515240989/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((84446513/156250000 : ℝ)*X 2 0+(5152409727/10000000000 : ℝ)*X 2 1+(-184810571/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((72423631/200000000 : ℝ)*X 0 0+(272726313/625000000 : ℝ)*X 0 1+(1090905167/2500000000 : ℝ)*X 0 2+(72423631/200000000 : ℝ)*X 1 0+(272726313/625000000 : ℝ)*X 1 1+(1090905167/2500000000 : ℝ)*X 1 2+(72423631/200000000 : ℝ)*X 2 0+(272726313/625000000 : ℝ)*X 2 1+(1090905167/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1711_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16689/25000 : ℝ) ≤ (-11792001545414594212937594525913/17665000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454061/25000000000000 : ℝ)*(upper0) + (7101367/100000000000000 : ℝ)*(upper3) + (959247/100000000000000 : ℝ)*(lower4) + (135918802031083/10000000000000 : ℝ)*(major0) + (135918802031083/10000000000000 : ℝ)*(major1) + (135918802031083/10000000000000 : ℝ)*(major2) + (486032823/100000000000000 : ℝ)*(sp1) + (34076653/50000000000000 : ℝ)*(sp3) + (1022325498533849/50000000000000 : ℝ)*(sp4) + (255581318524313/12500000000000 : ℝ)*(sp5) + (2044648665521837/100000000000000 : ℝ)*(sp6) + (86997012115823/12500000000000 : ℝ)*(sp7) + (37159629/100000000000000 : ℝ)*(sp8) + (236870549/10000000000000 : ℝ)*(sp14) + (695976165079889/100000000000000 : ℝ)*(f.failure) + (2044651034227327/100000000000000 : ℝ)*(f.sum) + (2698470801047/441625000000000000000000000 : ℝ)*base66 + (268613077973885657/35330000000000000000000000000000 : ℝ)*base68 + (360636680353545657/35330000000000000000000000000000 : ℝ)*base70 + (354525058900005657/35330000000000000000000000000000 : ℝ)*base72 + (22321204461187/1766500000000000000000000000 : ℝ)*base73 + (194183638732245657/35330000000000000000000000000000 : ℝ)*base76 + (237855874779925657/35330000000000000000000000000000 : ℝ)*base78 + (64852585833455657/35330000000000000000000000000000 : ℝ)*base80 + (7160554162453/883250000000000000000000000 : ℝ)*base82 + (3392147/10000000000000000000000 : ℝ)*base89 + (3392147/10000000000000000000000 : ℝ)*base91 + (3392147/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29213/50000 : ℝ) ≤ (103213935802604092954580562347157/176650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15873847/100000000000000 : ℝ)*(lower0) + (15980941/50000000000000 : ℝ)*(lower1) + (442521/4000000000000 : ℝ)*(lower4) + (1464288869991713/100000000000000 : ℝ)*(major0) + (1464288869991713/100000000000000 : ℝ)*(major1) + (1464288869991713/100000000000000 : ℝ)*(major2) + (107965267932489/5000000000000 : ℝ)*(sp0) + (1079653775327303/50000000000000 : ℝ)*(sp1) + (1079654076485373/50000000000000 : ℝ)*(sp2) + (374896572590269/50000000000000 : ℝ)*(sp3) + (664676311/100000000000000 : ℝ)*(sp5) + (62360171/100000000000000 : ℝ)*(sp6) + (107293997/50000000000000 : ℝ)*(sp7) + (2856681137/100000000000000 : ℝ)*(sp12) + (187448339942133/25000000000000 : ℝ)*(f.failure) + (539827053832729/25000000000000 : ℝ)*(f.sum) + (50323014263951/35330000000000000000000000000 : ℝ)*base65 + (1176778384477026427/353300000000000000000000000000000 : ℝ)*base68 + (1907874328687526427/353300000000000000000000000000000 : ℝ)*base70 + (676178849457326427/353300000000000000000000000000000 : ℝ)*base72 + (32844883395791/35330000000000000000000000000 : ℝ)*base73 + (3566037174838026427/353300000000000000000000000000000 : ℝ)*base76 + (1413265689755626427/353300000000000000000000000000000 : ℝ)*base78 + (1194107257330126427/353300000000000000000000000000000 : ℝ)*base80 + (151481067926869/35330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14144959/2500000000000000000000 : ℝ)*base89 + (14144959/2500000000000000000000 : ℝ)*base91 + (14144959/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40757/50000 : ℝ) ≤ (35999766441073369211931700640811/44162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5823119/100000000000000 : ℝ)*(upper0) + (1812157/4000000000000 : ℝ)*(upper1) + (1520811/2500000000000 : ℝ)*(upper2) + (742096957914403/50000000000000 : ℝ)*(major0) + (742096957914403/50000000000000 : ℝ)*(major1) + (742096957914403/50000000000000 : ℝ)*(major2) + (2487591651/20000000000000 : ℝ)*(sp1) + (10180866949/50000000000000 : ℝ)*(sp2) + (209980503/20000000000000 : ℝ)*(sp3) + (44881519/6250000000000 : ℝ)*(sp4) + (545307279727269/25000000000000 : ℝ)*(sp8) + (1090608699527563/50000000000000 : ℝ)*(sp9) + (1090604737639741/50000000000000 : ℝ)*(sp10) + (75998474627689/10000000000000 : ℝ)*(sp11) + (151997159235881/20000000000000 : ℝ)*(f.failure) + (2181229837013381/100000000000000 : ℝ)*(f.sum) + (36014491035241/17665000000000000000000000000 : ℝ)*base65 + (838466287141138063/176650000000000000000000000000000 : ℝ)*base67 + (1434193990278638063/176650000000000000000000000000000 : ℝ)*base69 + (447308762865988063/176650000000000000000000000000000 : ℝ)*base71 + (72882663755103/8832500000000000000000000000 : ℝ)*base73 + (33699698555911937/176650000000000000000000000000000 : ℝ)*base76 + (1191257123546638063/176650000000000000000000000000000 : ℝ)*base77 + (1441004048806338063/176650000000000000000000000000000 : ℝ)*base79 + (13728625429169/17665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (14558437/2000000000000000000000 : ℝ)*base90 + (14558437/2000000000000000000000 : ℝ)*base92 + (14558437/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-90437/100000 : ℝ) ≤ (-79876524455251936008190888030227/88325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14607677/12500000000000 : ℝ)*(upper3) + (40448553/100000000000000 : ℝ)*(lower4) + (2567221/10000000000000 : ℝ)*(upper5) + (1533549803424529/100000000000000 : ℝ)*(major0) + (1533549803424529/100000000000000 : ℝ)*(major1) + (1533549803424529/100000000000000 : ℝ)*(major2) + (2732409293/50000000000000 : ℝ)*(sp4) + (1912277441/2500000000000 : ℝ)*(sp5) + (88683597733/100000000000000 : ℝ)*(sp6) + (29725445299/100000000000000 : ℝ)*(sp7) + (1155990224561387/50000000000000 : ℝ)*(sp12) + (57797735571093/2500000000000 : ℝ)*(sp13) + (1155948615171813/50000000000000 : ℝ)*(sp14) + (785228896023671/100000000000000 : ℝ)*(sp15) + (78525862146897/10000000000000 : ℝ)*(f.failure) + (28899823924267/1250000000000 : ℝ)*(f.sum) + (108083397302267/35330000000000000000000000000 : ℝ)*base66 + (734226389804885909/353300000000000000000000000000000 : ℝ)*base67 + (1451041395454185909/353300000000000000000000000000000 : ℝ)*base69 + (1086770576113514091/353300000000000000000000000000000 : ℝ)*base72 + (166980136203493/35330000000000000000000000000 : ℝ)*base73 + (1375160012910585909/353300000000000000000000000000000 : ℝ)*base75 + (1808258836729385909/353300000000000000000000000000000 : ℝ)*base77 + (2240280386314085909/353300000000000000000000000000000 : ℝ)*base79 + (15063413363313/35330000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7628269/1000000000000000000000 : ℝ)*base90 + (7628269/1000000000000000000000 : ℝ)*base92 + (7628269/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1711_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3417/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16689/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29213/50000 : ℝ) else (40757/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90437/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1711_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1711_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16689/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29213/50000 : ℝ) else (40757/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90437/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1711_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1711_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1711_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5303/1024 : ℝ) ≤ p) (hpb : p ≤ (5311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (195292323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16689/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29213/50000 : ℝ) else (40757/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90437/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1711_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
