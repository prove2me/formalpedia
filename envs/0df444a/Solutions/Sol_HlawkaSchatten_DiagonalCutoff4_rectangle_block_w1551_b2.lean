-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:07.911801+00:00
-- url     : https://prove2.me/submissions/1fa93747-54b4-4ba3-b4b6-66269aeb6e5d

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
theorem support_rectangle_w1551_box_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1604996213/10000000000 : ℝ)*x 0 + (5398629221/10000000000 : ℝ)*x 1 + (5398630533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1604996213/10000000000 : ℝ)^4599 ≤ (1187969013051/12500000000000 : ℝ)^3575 := by
    have hnat : (1604996213 : ℕ)^4599*12500000000000^3575 ≤ 1187969013051^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604996213 10000000000 1187969013051 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398629221/10000000000 : ℝ)^4599 ≤ (2828007304147/6250000000000 : ℝ)^3575 := by
    have hnat : (5398629221 : ℕ)^4599*6250000000000^3575 ≤ 2828007304147^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398629221 10000000000 2828007304147 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398630533/10000000000 : ℝ)^4599 ≤ (45248131012501/100000000000000 : ℝ)^3575 := by
    have hnat : (5398630533 : ℕ)^4599*100000000000000^3575 ≤ 45248131012501^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398630533 10000000000 45248131012501 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1604996213/10000000000 : ℝ), (5398629221/10000000000 : ℝ), (5398630533/10000000000 : ℝ)] ![(1187969013051/12500000000000 : ℝ), (2828007304147/6250000000000 : ℝ), (45248131012501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1604996213/10000000000 : ℝ)|^4599 ≤ (1187969013051/12500000000000 : ℝ)^3575
        have hw : |(-1604996213/10000000000 : ℝ)|=(1604996213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398629221/10000000000 : ℝ)|^4599 ≤ (2828007304147/6250000000000 : ℝ)^3575
        have hw : |(5398629221/10000000000 : ℝ)|=(5398629221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398630533/10000000000 : ℝ)|^4599 ≤ (45248131012501/100000000000000 : ℝ)^3575
        have hw : |(5398630533/10000000000 : ℝ)|=(5398630533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317775861/2500000000 : ℝ)*x 0 + (-1782159127/10000000000 : ℝ)*x 1 + (1079726029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317775861/2500000000 : ℝ)^4599 ≤ (8775559212353/20000000000000 : ℝ)^3575 := by
    have hnat : (1317775861 : ℕ)^4599*20000000000000^3575 ≤ 8775559212353^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317775861 2500000000 8775559212353 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782159127/10000000000 : ℝ)^4599 ≤ (2718519273281/25000000000000 : ℝ)^3575 := by
    have hnat : (1782159127 : ℕ)^4599*25000000000000^3575 ≤ 2718519273281^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782159127 10000000000 2718519273281 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079726029/2000000000 : ℝ)^4599 ≤ (11312031707259/25000000000000 : ℝ)^3575 := by
    have hnat : (1079726029 : ℕ)^4599*25000000000000^3575 ≤ 11312031707259^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079726029 2000000000 11312031707259 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317775861/2500000000 : ℝ), (-1782159127/10000000000 : ℝ), (1079726029/2000000000 : ℝ)] ![(8775559212353/20000000000000 : ℝ), (2718519273281/25000000000000 : ℝ), (11312031707259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317775861/2500000000 : ℝ)|^4599 ≤ (8775559212353/20000000000000 : ℝ)^3575
        have hw : |(1317775861/2500000000 : ℝ)|=(1317775861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782159127/10000000000 : ℝ)|^4599 ≤ (2718519273281/25000000000000 : ℝ)^3575
        have hw : |(-1782159127/10000000000 : ℝ)|=(1782159127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079726029/2000000000 : ℝ)|^4599 ≤ (11312031707259/25000000000000 : ℝ)^3575
        have hw : |(1079726029/2000000000 : ℝ)|=(1079726029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658887897/1250000000 : ℝ)*x 0 + (2699315297/5000000000 : ℝ)*x 1 + (-14257271/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658887897/1250000000 : ℝ)^4599 ≤ (21938896595937/50000000000000 : ℝ)^3575 := by
    have hnat : (658887897 : ℕ)^4599*50000000000000^3575 ≤ 21938896595937^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658887897 1250000000 21938896595937 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699315297/5000000000 : ℝ)^4599 ≤ (4524813167021/10000000000000 : ℝ)^3575 := by
    have hnat : (2699315297 : ℕ)^4599*10000000000000^3575 ≤ 4524813167021^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699315297 5000000000 4524813167021 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14257271/80000000 : ℝ)^4599 ≤ (1087407511509/10000000000000 : ℝ)^3575 := by
    have hnat : (14257271 : ℕ)^4599*10000000000000^3575 ≤ 1087407511509^3575*80000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14257271 80000000 1087407511509 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658887897/1250000000 : ℝ), (2699315297/5000000000 : ℝ), (-14257271/80000000 : ℝ)] ![(21938896595937/50000000000000 : ℝ), (4524813167021/10000000000000 : ℝ), (1087407511509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658887897/1250000000 : ℝ)|^4599 ≤ (21938896595937/50000000000000 : ℝ)^3575
        have hw : |(658887897/1250000000 : ℝ)|=(658887897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699315297/5000000000 : ℝ)|^4599 ≤ (4524813167021/10000000000000 : ℝ)^3575
        have hw : |(2699315297/5000000000 : ℝ)|=(2699315297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14257271/80000000 : ℝ)|^4599 ≤ (1087407511509/10000000000000 : ℝ)^3575
        have hw : |(-14257271/80000000 : ℝ)|=(14257271/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4453362889/10000000000 : ℝ)*x 0 + (4157986203/10000000000 : ℝ)*x 1 + (4157984551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453362889/10000000000 : ℝ)^4599 ≤ (2207702647821/6250000000000 : ℝ)^3575 := by
    have hnat : (4453362889 : ℕ)^4599*6250000000000^3575 ≤ 2207702647821^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453362889 10000000000 2207702647821 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4157986203/10000000000 : ℝ)^4599 ≤ (808459676761/2500000000000 : ℝ)^3575 := by
    have hnat : (4157986203 : ℕ)^4599*2500000000000^3575 ≤ 808459676761^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157986203 10000000000 808459676761 2500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157984551/10000000000 : ℝ)^4599 ≤ (2021148158873/6250000000000 : ℝ)^3575 := by
    have hnat : (4157984551 : ℕ)^4599*6250000000000^3575 ≤ 2021148158873^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157984551 10000000000 2021148158873 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453362889/10000000000 : ℝ), (4157986203/10000000000 : ℝ), (4157984551/10000000000 : ℝ)] ![(2207702647821/6250000000000 : ℝ), (808459676761/2500000000000 : ℝ), (2021148158873/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453362889/10000000000 : ℝ)|^4599 ≤ (2207702647821/6250000000000 : ℝ)^3575
        have hw : |(4453362889/10000000000 : ℝ)|=(4453362889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4157986203/10000000000 : ℝ)|^4599 ≤ (808459676761/2500000000000 : ℝ)^3575
        have hw : |(4157986203/10000000000 : ℝ)|=(4157986203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157984551/10000000000 : ℝ)|^4599 ≤ (2021148158873/6250000000000 : ℝ)^3575
        have hw : |(4157984551/10000000000 : ℝ)|=(4157984551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8096873/40000000 : ℝ)*x 0 + (1048935973/2000000000 : ℝ)*x 1 + (1311170091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8096873/40000000 : ℝ)^4599 ≤ (1280991212843/10000000000000 : ℝ)^3575 := by
    have hnat : (8096873 : ℕ)^4599*10000000000000^3575 ≤ 1280991212843^3575*40000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8096873 40000000 1280991212843 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048935973/2000000000 : ℝ)^4599 ≤ (43595041258293/100000000000000 : ℝ)^3575 := by
    have hnat : (1048935973 : ℕ)^4599*100000000000000^3575 ≤ 43595041258293^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048935973 2000000000 43595041258293 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311170091/2500000000 : ℝ)^4599 ≤ (43595046594173/100000000000000 : ℝ)^3575 := by
    have hnat : (1311170091 : ℕ)^4599*100000000000000^3575 ≤ 43595046594173^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311170091 2500000000 43595046594173 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8096873/40000000 : ℝ), (1048935973/2000000000 : ℝ), (1311170091/2500000000 : ℝ)] ![(1280991212843/10000000000000 : ℝ), (43595041258293/100000000000000 : ℝ), (43595046594173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8096873/40000000 : ℝ)|^4599 ≤ (1280991212843/10000000000000 : ℝ)^3575
        have hw : |(-8096873/40000000 : ℝ)|=(8096873/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048935973/2000000000 : ℝ)|^4599 ≤ (43595041258293/100000000000000 : ℝ)^3575
        have hw : |(1048935973/2000000000 : ℝ)|=(1048935973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311170091/2500000000 : ℝ)|^4599 ≤ (43595046594173/100000000000000 : ℝ)^3575
        have hw : |(1311170091/2500000000 : ℝ)|=(1311170091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336123073/625000000 : ℝ)*x 0 + (-1846218823/10000000000 : ℝ)*x 1 + (5244680671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336123073/625000000 : ℝ)^4599 ≤ (5628184973523/12500000000000 : ℝ)^3575 := by
    have hnat : (336123073 : ℕ)^4599*12500000000000^3575 ≤ 5628184973523^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336123073 625000000 5628184973523 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846218823/10000000000 : ℝ)^4599 ≤ (2844867579699/25000000000000 : ℝ)^3575 := by
    have hnat : (1846218823 : ℕ)^4599*25000000000000^3575 ≤ 2844867579699^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846218823 10000000000 2844867579699 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244680671/10000000000 : ℝ)^4599 ≤ (5449381234621/12500000000000 : ℝ)^3575 := by
    have hnat : (5244680671 : ℕ)^4599*12500000000000^3575 ≤ 5449381234621^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244680671 10000000000 5449381234621 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336123073/625000000 : ℝ), (-1846218823/10000000000 : ℝ), (5244680671/10000000000 : ℝ)] ![(5628184973523/12500000000000 : ℝ), (2844867579699/25000000000000 : ℝ), (5449381234621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336123073/625000000 : ℝ)|^4599 ≤ (5628184973523/12500000000000 : ℝ)^3575
        have hw : |(336123073/625000000 : ℝ)|=(336123073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1846218823/10000000000 : ℝ)|^4599 ≤ (2844867579699/25000000000000 : ℝ)^3575
        have hw : |(-1846218823/10000000000 : ℝ)|=(1846218823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244680671/10000000000 : ℝ)|^4599 ≤ (5449381234621/12500000000000 : ℝ)^3575
        have hw : |(5244680671/10000000000 : ℝ)|=(5244680671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268898493/500000000 : ℝ)*x 0 + (5244679829/10000000000 : ℝ)*x 1 + (-923109509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268898493/500000000 : ℝ)^4599 ≤ (1801019489649/4000000000000 : ℝ)^3575 := by
    have hnat : (268898493 : ℕ)^4599*4000000000000^3575 ≤ 1801019489649^3575*500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268898493 500000000 1801019489649 4000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244679829/10000000000 : ℝ)^4599 ≤ (2179752043667/5000000000000 : ℝ)^3575 := by
    have hnat : (5244679829 : ℕ)^4599*5000000000000^3575 ≤ 2179752043667^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244679829 10000000000 2179752043667 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923109509/5000000000 : ℝ)^4599 ≤ (11379471864979/100000000000000 : ℝ)^3575 := by
    have hnat : (923109509 : ℕ)^4599*100000000000000^3575 ≤ 11379471864979^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923109509 5000000000 11379471864979 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268898493/500000000 : ℝ), (5244679829/10000000000 : ℝ), (-923109509/5000000000 : ℝ)] ![(1801019489649/4000000000000 : ℝ), (2179752043667/5000000000000 : ℝ), (11379471864979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268898493/500000000 : ℝ)|^4599 ≤ (1801019489649/4000000000000 : ℝ)^3575
        have hw : |(268898493/500000000 : ℝ)|=(268898493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244679829/10000000000 : ℝ)|^4599 ≤ (2179752043667/5000000000000 : ℝ)^3575
        have hw : |(5244679829/10000000000 : ℝ)|=(5244679829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-923109509/5000000000 : ℝ)|^4599 ≤ (11379471864979/100000000000000 : ℝ)^3575
        have hw : |(-923109509/5000000000 : ℝ)|=(923109509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2023966569/5000000000 : ℝ)*x 0 + (4360571773/10000000000 : ℝ)*x 1 + (4360569663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023966569/5000000000 : ℝ)^4599 ≤ (31241492442533/100000000000000 : ℝ)^3575 := by
    have hnat : (2023966569 : ℕ)^4599*100000000000000^3575 ≤ 31241492442533^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023966569 5000000000 31241492442533 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4360571773/10000000000 : ℝ)^4599 ≤ (3437926447063/10000000000000 : ℝ)^3575 := by
    have hnat : (4360571773 : ℕ)^4599*10000000000000^3575 ≤ 3437926447063^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360571773 10000000000 3437926447063 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4360569663/10000000000 : ℝ)^4599 ≤ (34379243070179/100000000000000 : ℝ)^3575 := by
    have hnat : (4360569663 : ℕ)^4599*100000000000000^3575 ≤ 34379243070179^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360569663 10000000000 34379243070179 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2023966569/5000000000 : ℝ), (4360571773/10000000000 : ℝ), (4360569663/10000000000 : ℝ)] ![(31241492442533/100000000000000 : ℝ), (3437926447063/10000000000000 : ℝ), (34379243070179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2023966569/5000000000 : ℝ)|^4599 ≤ (31241492442533/100000000000000 : ℝ)^3575
        have hw : |(2023966569/5000000000 : ℝ)|=(2023966569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4360571773/10000000000 : ℝ)|^4599 ≤ (3437926447063/10000000000000 : ℝ)^3575
        have hw : |(4360571773/10000000000 : ℝ)|=(4360571773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4360569663/10000000000 : ℝ)|^4599 ≤ (34379243070179/100000000000000 : ℝ)^3575
        have hw : |(4360569663/10000000000 : ℝ)|=(4360569663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_8 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935439359/10000000000 : ℝ)*x 0 + (5136414523/10000000000 : ℝ)*x 1 + (5418961703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935439359/10000000000 : ℝ)^4599 ≤ (1511469227929/12500000000000 : ℝ)^3575 := by
    have hnat : (1935439359 : ℕ)^4599*12500000000000^3575 ≤ 1511469227929^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935439359 10000000000 1511469227929 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136414523/10000000000 : ℝ)^4599 ≤ (21220391897117/50000000000000 : ℝ)^3575 := by
    have hnat : (5136414523 : ℕ)^4599*50000000000000^3575 ≤ 21220391897117^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136414523 10000000000 21220391897117 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418961703/10000000000 : ℝ)^4599 ≤ (22733731188163/50000000000000 : ℝ)^3575 := by
    have hnat : (5418961703 : ℕ)^4599*50000000000000^3575 ≤ 22733731188163^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418961703 10000000000 22733731188163 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935439359/10000000000 : ℝ), (5136414523/10000000000 : ℝ), (5418961703/10000000000 : ℝ)] ![(1511469227929/12500000000000 : ℝ), (21220391897117/50000000000000 : ℝ), (22733731188163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935439359/10000000000 : ℝ)|^4599 ≤ (1511469227929/12500000000000 : ℝ)^3575
        have hw : |(-1935439359/10000000000 : ℝ)|=(1935439359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136414523/10000000000 : ℝ)|^4599 ≤ (21220391897117/50000000000000 : ℝ)^3575
        have hw : |(5136414523/10000000000 : ℝ)|=(5136414523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418961703/10000000000 : ℝ)|^4599 ≤ (22733731188163/50000000000000 : ℝ)^3575
        have hw : |(5418961703/10000000000 : ℝ)|=(5418961703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_9 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256986163/10000000000 : ℝ)*x 0 + (-177346193/1000000000 : ℝ)*x 1 + (1083792369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256986163/10000000000 : ℝ)^4599 ≤ (10931669622311/25000000000000 : ℝ)^3575 := by
    have hnat : (5256986163 : ℕ)^4599*25000000000000^3575 ≤ 10931669622311^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256986163 10000000000 10931669622311 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177346193/1000000000 : ℝ)^4599 ≤ (10805857581921/100000000000000 : ℝ)^3575 := by
    have hnat : (177346193 : ℕ)^4599*100000000000000^3575 ≤ 10805857581921^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177346193 1000000000 10805857581921 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083792369/2000000000 : ℝ)^4599 ≤ (45467463909037/100000000000000 : ℝ)^3575 := by
    have hnat : (1083792369 : ℕ)^4599*100000000000000^3575 ≤ 45467463909037^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083792369 2000000000 45467463909037 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256986163/10000000000 : ℝ), (-177346193/1000000000 : ℝ), (1083792369/2000000000 : ℝ)] ![(10931669622311/25000000000000 : ℝ), (10805857581921/100000000000000 : ℝ), (45467463909037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256986163/10000000000 : ℝ)|^4599 ≤ (10931669622311/25000000000000 : ℝ)^3575
        have hw : |(5256986163/10000000000 : ℝ)|=(5256986163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177346193/1000000000 : ℝ)|^4599 ≤ (10805857581921/100000000000000 : ℝ)^3575
        have hw : |(-177346193/1000000000 : ℝ)|=(177346193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083792369/2000000000 : ℝ)|^4599 ≤ (45467463909037/100000000000000 : ℝ)^3575
        have hw : |(1083792369/2000000000 : ℝ)|=(1083792369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_10 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256985309/10000000000 : ℝ)*x 0 + (5418962633/10000000000 : ℝ)*x 1 + (-443365503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256985309/10000000000 : ℝ)^4599 ≤ (8745333870233/20000000000000 : ℝ)^3575 := by
    have hnat : (5256985309 : ℕ)^4599*20000000000000^3575 ≤ 8745333870233^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256985309 10000000000 8745333870233 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418962633/10000000000 : ℝ)^4599 ≤ (22733736207253/50000000000000 : ℝ)^3575 := by
    have hnat : (5418962633 : ℕ)^4599*50000000000000^3575 ≤ 22733736207253^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418962633 10000000000 22733736207253 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443365503/2500000000 : ℝ)^4599 ≤ (5402929112333/50000000000000 : ℝ)^3575 := by
    have hnat : (443365503 : ℕ)^4599*50000000000000^3575 ≤ 5402929112333^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443365503 2500000000 5402929112333 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256985309/10000000000 : ℝ), (5418962633/10000000000 : ℝ), (-443365503/2500000000 : ℝ)] ![(8745333870233/20000000000000 : ℝ), (22733736207253/50000000000000 : ℝ), (5402929112333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256985309/10000000000 : ℝ)|^4599 ≤ (8745333870233/20000000000000 : ℝ)^3575
        have hw : |(5256985309/10000000000 : ℝ)|=(5256985309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418962633/10000000000 : ℝ)|^4599 ≤ (22733736207253/50000000000000 : ℝ)^3575
        have hw : |(5418962633/10000000000 : ℝ)|=(5418962633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443365503/2500000000 : ℝ)|^4599 ≤ (5402929112333/50000000000000 : ℝ)^3575
        have hw : |(-443365503/2500000000 : ℝ)|=(443365503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_11 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1126440381/2500000000 : ℝ)*x 0 + (1032799171/2500000000 : ℝ)*x 1 + (2065597951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126440381/2500000000 : ℝ)^4599 ≤ (7171760684919/20000000000000 : ℝ)^3575 := by
    have hnat : (1126440381 : ℕ)^4599*20000000000000^3575 ≤ 7171760684919^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126440381 2500000000 7171760684919 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032799171/2500000000 : ℝ)^4599 ≤ (8017650547641/25000000000000 : ℝ)^3575 := by
    have hnat : (1032799171 : ℕ)^4599*25000000000000^3575 ≤ 8017650547641^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032799171 2500000000 8017650547641 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065597951/5000000000 : ℝ)^4599 ≤ (16035297190513/50000000000000 : ℝ)^3575 := by
    have hnat : (2065597951 : ℕ)^4599*50000000000000^3575 ≤ 16035297190513^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065597951 5000000000 16035297190513 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126440381/2500000000 : ℝ), (1032799171/2500000000 : ℝ), (2065597951/5000000000 : ℝ)] ![(7171760684919/20000000000000 : ℝ), (8017650547641/25000000000000 : ℝ), (16035297190513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126440381/2500000000 : ℝ)|^4599 ≤ (7171760684919/20000000000000 : ℝ)^3575
        have hw : |(1126440381/2500000000 : ℝ)|=(1126440381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032799171/2500000000 : ℝ)|^4599 ≤ (8017650547641/25000000000000 : ℝ)^3575
        have hw : |(1032799171/2500000000 : ℝ)|=(1032799171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065597951/5000000000 : ℝ)|^4599 ≤ (16035297190513/50000000000000 : ℝ)^3575
        have hw : |(2065597951/5000000000 : ℝ)|=(2065597951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_12 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-846762807/5000000000 : ℝ)*x 0 + (220141601/400000000 : ℝ)*x 1 + (5229633123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846762807/5000000000 : ℝ)^4599 ≤ (5091688776153/50000000000000 : ℝ)^3575 := by
    have hnat : (846762807 : ℕ)^4599*50000000000000^3575 ≤ 5091688776153^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846762807 5000000000 5091688776153 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220141601/400000000 : ℝ)^4599 ≤ (4638241201053/10000000000000 : ℝ)^3575 := by
    have hnat : (220141601 : ℕ)^4599*10000000000000^3575 ≤ 4638241201053^3575*400000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220141601 400000000 4638241201053 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229633123/10000000000 : ℝ)^4599 ≤ (43434210413093/100000000000000 : ℝ)^3575 := by
    have hnat : (5229633123 : ℕ)^4599*100000000000000^3575 ≤ 43434210413093^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229633123 10000000000 43434210413093 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-846762807/5000000000 : ℝ), (220141601/400000000 : ℝ), (5229633123/10000000000 : ℝ)] ![(5091688776153/50000000000000 : ℝ), (4638241201053/10000000000000 : ℝ), (43434210413093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-846762807/5000000000 : ℝ)|^4599 ≤ (5091688776153/50000000000000 : ℝ)^3575
        have hw : |(-846762807/5000000000 : ℝ)|=(846762807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220141601/400000000 : ℝ)|^4599 ≤ (4638241201053/10000000000000 : ℝ)^3575
        have hw : |(220141601/400000000 : ℝ)|=(220141601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229633123/10000000000 : ℝ)|^4599 ≤ (43434210413093/100000000000000 : ℝ)^3575
        have hw : |(5229633123/10000000000 : ℝ)|=(5229633123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_13 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388415289/10000000000 : ℝ)*x 0 + (-1852307507/10000000000 : ℝ)*x 1 + (1045926617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388415289/10000000000 : ℝ)^4599 ≤ (22569009412981/50000000000000 : ℝ)^3575 := by
    have hnat : (5388415289 : ℕ)^4599*50000000000000^3575 ≤ 22569009412981^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388415289 10000000000 22569009412981 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852307507/10000000000 : ℝ)^4599 ≤ (11427771148073/100000000000000 : ℝ)^3575 := by
    have hnat : (1852307507 : ℕ)^4599*100000000000000^3575 ≤ 11427771148073^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852307507 10000000000 11427771148073 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045926617/2000000000 : ℝ)^4599 ≤ (2714638125443/6250000000000 : ℝ)^3575 := by
    have hnat : (1045926617 : ℕ)^4599*6250000000000^3575 ≤ 2714638125443^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045926617 2000000000 2714638125443 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388415289/10000000000 : ℝ), (-1852307507/10000000000 : ℝ), (1045926617/2000000000 : ℝ)] ![(22569009412981/50000000000000 : ℝ), (11427771148073/100000000000000 : ℝ), (2714638125443/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388415289/10000000000 : ℝ)|^4599 ≤ (22569009412981/50000000000000 : ℝ)^3575
        have hw : |(5388415289/10000000000 : ℝ)|=(5388415289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852307507/10000000000 : ℝ)|^4599 ≤ (11427771148073/100000000000000 : ℝ)^3575
        have hw : |(-1852307507/10000000000 : ℝ)|=(1852307507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045926617/2000000000 : ℝ)|^4599 ≤ (2714638125443/6250000000000 : ℝ)^3575
        have hw : |(1045926617/2000000000 : ℝ)|=(1045926617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_14 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694207427/5000000000 : ℝ)*x 0 + (2614816763/5000000000 : ℝ)*x 1 + (-370461501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694207427/5000000000 : ℝ)^4599 ≤ (45138014138281/100000000000000 : ℝ)^3575 := by
    have hnat : (2694207427 : ℕ)^4599*100000000000000^3575 ≤ 45138014138281^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694207427 5000000000 45138014138281 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614816763/5000000000 : ℝ)^4599 ≤ (21717107359443/50000000000000 : ℝ)^3575 := by
    have hnat : (2614816763 : ℕ)^4599*50000000000000^3575 ≤ 21717107359443^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614816763 5000000000 21717107359443 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370461501/2000000000 : ℝ)^4599 ≤ (57138855661/500000000000 : ℝ)^3575 := by
    have hnat : (370461501 : ℕ)^4599*500000000000^3575 ≤ 57138855661^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370461501 2000000000 57138855661 500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694207427/5000000000 : ℝ), (2614816763/5000000000 : ℝ), (-370461501/2000000000 : ℝ)] ![(45138014138281/100000000000000 : ℝ), (21717107359443/50000000000000 : ℝ), (57138855661/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694207427/5000000000 : ℝ)|^4599 ≤ (45138014138281/100000000000000 : ℝ)^3575
        have hw : |(2694207427/5000000000 : ℝ)|=(2694207427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614816763/5000000000 : ℝ)|^4599 ≤ (21717107359443/50000000000000 : ℝ)^3575
        have hw : |(2614816763/5000000000 : ℝ)|=(2614816763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370461501/2000000000 : ℝ)|^4599 ≤ (57138855661/500000000000 : ℝ)^3575
        have hw : |(-370461501/2000000000 : ℝ)|=(370461501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_box_15 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1001860769/2500000000 : ℝ)*x 0 + (4380347593/10000000000 : ℝ)*x 1 + (4380347623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001860769/2500000000 : ℝ)^4599 ≤ (1927503883039/6250000000000 : ℝ)^3575 := by
    have hnat : (1001860769 : ℕ)^4599*6250000000000^3575 ≤ 1927503883039^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001860769 2500000000 1927503883039 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380347593/10000000000 : ℝ)^4599 ≤ (17289984387967/50000000000000 : ℝ)^3575 := by
    have hnat : (4380347593 : ℕ)^4599*50000000000000^3575 ≤ 17289984387967^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380347593 10000000000 17289984387967 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4380347623/10000000000 : ℝ)^4599 ≤ (172899845403/500000000000 : ℝ)^3575 := by
    have hnat : (4380347623 : ℕ)^4599*500000000000^3575 ≤ 172899845403^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380347623 10000000000 172899845403 500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001860769/2500000000 : ℝ), (4380347593/10000000000 : ℝ), (4380347623/10000000000 : ℝ)] ![(1927503883039/6250000000000 : ℝ), (17289984387967/50000000000000 : ℝ), (172899845403/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001860769/2500000000 : ℝ)|^4599 ≤ (1927503883039/6250000000000 : ℝ)^3575
        have hw : |(1001860769/2500000000 : ℝ)|=(1001860769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380347593/10000000000 : ℝ)|^4599 ≤ (17289984387967/50000000000000 : ℝ)^3575
        have hw : |(4380347593/10000000000 : ℝ)|=(4380347593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4380347623/10000000000 : ℝ)|^4599 ≤ (172899845403/500000000000 : ℝ)^3575
        have hw : |(4380347623/10000000000 : ℝ)|=(4380347623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63797/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14703/25000 : ℝ) ∧ (10091/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86249/100000 : ℝ) := by
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
  have lower0 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5529/50000 : ℝ) ^ (4597/1024 : ℝ) ≤ (5091170489669217/100000000000000000000 : ℝ) := by
    have hpowers : (5529/50000 : ℝ)^4597 ≤ (5091170489669217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5529 : ℕ)^4597*100000000000000000000^1024 ≤ 5091170489669217^1024*50000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5529 50000 5091170489669217 100000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5529/50000 : ℝ)) (X := (5091170489669217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4597/1024 : ℝ) ≤ (5770887099856513/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4597 ≤ (5770887099856513/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4597*25000000000000000000^1024 ≤ 5770887099856513^1024*20000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5770887099856513 25000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5770887099856513/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005091170489669217/50000000000000000000 : ℝ) ≤ (10000226806712921/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50005091170489669217/50000000000000000000 : ℝ)^1024 ≤ (10000226806712921/10000000000000000 : ℝ)^4597 := by
      have hnat : (50005091170489669217 : ℕ)^1024*10000000000000000^4597 ≤ 10000226806712921^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005091170489669217 50000000000000000000 10000226806712921 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000226806712921/10000000000000000 : ℝ)) (X := (50005091170489669217/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028174718889095269/100000000000000000000 : ℝ) ≤ (10000627534341613/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (100028174718889095269/100000000000000000000 : ℝ)^1024 ≤ (10000627534341613/10000000000000000 : ℝ)^4597 := by
      have hnat : (100028174718889095269 : ℕ)^1024*10000000000000000^4597 ≤ 10000627534341613^4597*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028174718889095269 100000000000000000000 10000627534341613 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000627534341613/10000000000000000 : ℝ)) (X := (100028174718889095269/100000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505770887099856513/12500000000000000000 : ℝ) ≤ (2000205652394061/2000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (12505770887099856513/12500000000000000000 : ℝ)^1024 ≤ (2000205652394061/2000000000000000 : ℝ)^4597 := by
      have hnat : (12505770887099856513 : ℕ)^1024*2000000000000000^4597 ≤ 2000205652394061^4597*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505770887099856513 12500000000000000000 2000205652394061 2000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000205652394061/2000000000000000 : ℝ)) (X := (12505770887099856513/12500000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5091170489669217/100000000000000000000 : ℝ) ≤ ((465917279800862621/466000000000000000 : ℝ)+2*(100181907173/110675000000000 : ℝ)*(5529/50000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (465917279800862621/466000000000000000 : ℝ)+2*(100181907173/110675000000000 : ℝ)*(5529/50000 : ℝ)=(10000226806712921/10000000000000000 : ℝ) by norm_num, show 1+2*(5091170489669217/100000000000000000000 : ℝ)=(50005091170489669217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5770887099856513/25000000000000000000 : ℝ)+(5091170489669217/100000000000000000000 : ℝ) ≤ ((465917279800862621/466000000000000000 : ℝ)+(100181907173/110675000000000 : ℝ)*((3097/20000 : ℝ)+(5529/50000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (465917279800862621/466000000000000000 : ℝ)+(100181907173/110675000000000 : ℝ)*((3097/20000 : ℝ)+(5529/50000 : ℝ))=(10000627534341613/10000000000000000 : ℝ) by norm_num, show 1+(5770887099856513/25000000000000000000 : ℝ)+(5091170489669217/100000000000000000000 : ℝ)=(100028174718889095269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5770887099856513/25000000000000000000 : ℝ) ≤ ((465917279800862621/466000000000000000 : ℝ)+2*(100181907173/110675000000000 : ℝ)*(3097/20000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (465917279800862621/466000000000000000 : ℝ)+2*(100181907173/110675000000000 : ℝ)*(3097/20000 : ℝ)=(2000205652394061/2000000000000000 : ℝ) by norm_num, show 1+2*(5770887099856513/25000000000000000000 : ℝ)=(12505770887099856513/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (465917279800862621/466000000000000000 : ℝ)*(X 1 0+X 2 0)+(100181907173/110675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (465917279800862621/466000000000000000 : ℝ)) (alpha := (100181907173/110675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (465917279800862621/466000000000000000 : ℝ)*(X 0 1+X 2 1)+(100181907173/110675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (465917279800862621/466000000000000000 : ℝ)) (alpha := (100181907173/110675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (465917279800862621/466000000000000000 : ℝ)*(X 0 2+X 1 2)+(100181907173/110675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (465917279800862621/466000000000000000 : ℝ)) (alpha := (100181907173/110675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1604996213/10000000000 : ℝ)*X 0 0+(5398629221/10000000000 : ℝ)*X 0 1+(5398630533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317775861/2500000000 : ℝ)*X 1 0+(-1782159127/10000000000 : ℝ)*X 1 1+(1079726029/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((658887897/1250000000 : ℝ)*X 2 0+(2699315297/5000000000 : ℝ)*X 2 1+(-14257271/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4453362889/10000000000 : ℝ)*X 0 0+(4157986203/10000000000 : ℝ)*X 0 1+(4157984551/10000000000 : ℝ)*X 0 2+(4453362889/10000000000 : ℝ)*X 1 0+(4157986203/10000000000 : ℝ)*X 1 1+(4157984551/10000000000 : ℝ)*X 1 2+(4453362889/10000000000 : ℝ)*X 2 0+(4157986203/10000000000 : ℝ)*X 2 1+(4157984551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8096873/40000000 : ℝ)*X 0 0+(1048935973/2000000000 : ℝ)*X 0 1+(1311170091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((336123073/625000000 : ℝ)*X 1 0+(-1846218823/10000000000 : ℝ)*X 1 1+(5244680671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268898493/500000000 : ℝ)*X 2 0+(5244679829/10000000000 : ℝ)*X 2 1+(-923109509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2023966569/5000000000 : ℝ)*X 0 0+(4360571773/10000000000 : ℝ)*X 0 1+(4360569663/10000000000 : ℝ)*X 0 2+(2023966569/5000000000 : ℝ)*X 1 0+(4360571773/10000000000 : ℝ)*X 1 1+(4360569663/10000000000 : ℝ)*X 1 2+(2023966569/5000000000 : ℝ)*X 2 0+(4360571773/10000000000 : ℝ)*X 2 1+(4360569663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1935439359/10000000000 : ℝ)*X 0 0+(5136414523/10000000000 : ℝ)*X 0 1+(5418961703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256986163/10000000000 : ℝ)*X 1 0+(-177346193/1000000000 : ℝ)*X 1 1+(1083792369/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256985309/10000000000 : ℝ)*X 2 0+(5418962633/10000000000 : ℝ)*X 2 1+(-443365503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1126440381/2500000000 : ℝ)*X 0 0+(1032799171/2500000000 : ℝ)*X 0 1+(2065597951/5000000000 : ℝ)*X 0 2+(1126440381/2500000000 : ℝ)*X 1 0+(1032799171/2500000000 : ℝ)*X 1 1+(2065597951/5000000000 : ℝ)*X 1 2+(1126440381/2500000000 : ℝ)*X 2 0+(1032799171/2500000000 : ℝ)*X 2 1+(2065597951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-846762807/5000000000 : ℝ)*X 0 0+(220141601/400000000 : ℝ)*X 0 1+(5229633123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5388415289/10000000000 : ℝ)*X 1 0+(-1852307507/10000000000 : ℝ)*X 1 1+(1045926617/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2694207427/5000000000 : ℝ)*X 2 0+(2614816763/5000000000 : ℝ)*X 2 1+(-370461501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1001860769/2500000000 : ℝ)*X 0 0+(4380347593/10000000000 : ℝ)*X 0 1+(4380347623/10000000000 : ℝ)*X 0 2+(1001860769/2500000000 : ℝ)*X 1 0+(4380347593/10000000000 : ℝ)*X 1 1+(4380347623/10000000000 : ℝ)*X 1 2+(1001860769/2500000000 : ℝ)*X 2 0+(4380347593/10000000000 : ℝ)*X 2 1+(4380347623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63797/100000 : ℝ) ≤ (-464500207861836238583864886753/728125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125800689/50000000000000 : ℝ)*(lower0) + (862699/20000000000000 : ℝ)*(upper1) + (2490803/4000000000000 : ℝ)*(lower2) + (71262176176031/3125000000000 : ℝ)*(major0) + (71262176176031/3125000000000 : ℝ)*(major1) + (71262176176031/3125000000000 : ℝ)*(major2) + (3430016237/25000000000000 : ℝ)*(sp2) + (803112955342907/25000000000000 : ℝ)*(sp4) + (803110945462919/25000000000000 : ℝ)*(sp5) + (1606221449610009/50000000000000 : ℝ)*(sp6) + (684784979902441/50000000000000 : ℝ)*(sp7) + (4797913337/100000000000000 : ℝ)*(sp8) + (12837433289/100000000000000 : ℝ)*(sp13) + (8684748707/50000000000000 : ℝ)*(sp15) + (1369587329302297/100000000000000 : ℝ)*(f.failure) + (642491323856993/20000000000000 : ℝ)*(f.sum) + (56099853659131/22135000000000000000000000000 : ℝ)*base66 + (136961323058916519/27668750000000000000000000000000 : ℝ)*base67 + (162422011849766519/27668750000000000000000000000000 : ℝ)*base69 + (134170030110354019/27668750000000000000000000000000 : ℝ)*base71 + (10815610693831/22135000000000000000000000000 : ℝ)*base74 + (441691679737479019/27668750000000000000000000000000 : ℝ)*base75 + (120367286358727231/27668750000000000000000000000000 : ℝ)*base78 + (135890529043589731/27668750000000000000000000000000 : ℝ)*base80 + (24944972500853/2766875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (759121/156250000000000000000 : ℝ)*base89 + (759121/156250000000000000000 : ℝ)*base91 + (759121/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14703/25000 : ℝ) ≤ (65092969196246604054129769715061/110675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1173687/1000000000000 : ℝ)*(upper1) + (140628981/100000000000000 : ℝ)*(upper3) + (89904347/100000000000000 : ℝ)*(upper4) + (1179658463034287/50000000000000 : ℝ)*(major0) + (1179658463034287/50000000000000 : ℝ)*(major1) + (1179658463034287/50000000000000 : ℝ)*(major2) + (3282025866517199/100000000000000 : ℝ)*(sp0) + (328203441801083/10000000000000 : ℝ)*(sp1) + (1641008887301083/50000000000000 : ℝ)*(sp2) + (1416988060847237/100000000000000 : ℝ)*(sp3) + (2021986587/50000000000000 : ℝ)*(sp5) + (258592273/1250000000000 : ℝ)*(sp6) + (2489550979/100000000000000 : ℝ)*(sp7) + (12595466807/100000000000000 : ℝ)*(sp12) + (177123818799777/12500000000000 : ℝ)*(f.failure) + (1641019230992003/50000000000000 : ℝ)*(f.sum) + (35416342118679/11067500000000000000000000000 : ℝ)*base65 + (2090251551079718313/442700000000000000000000000000000 : ℝ)*base67 + (7117094748612281687/442700000000000000000000000000000 : ℝ)*base70 + (9068169294489218313/442700000000000000000000000000000 : ℝ)*base71 + (20370712603851/11067500000000000000000000000 : ℝ)*base74 + (1263435487052518313/442700000000000000000000000000000 : ℝ)*base75 + (4846128829896418313/442700000000000000000000000000000 : ℝ)*base77 + (2660781260192718313/442700000000000000000000000000000 : ℝ)*base79 + (270231057748741/11067500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base86 + (57307/9765625000000000000 : ℝ)*base90 + (57307/9765625000000000000 : ℝ)*base92 + (57307/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10091/12500 : ℝ) ≤ (89348551612315201864713433864551/110675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24030799/100000000000000 : ℝ)*(upper1) + (73622643/100000000000000 : ℝ)*(upper2) + (20460939/20000000000000 : ℝ)*(upper3) + (81608731/50000000000000 : ℝ)*(lower5) + (637082449068117/25000000000000 : ℝ)*(major0) + (637082449068117/25000000000000 : ℝ)*(major1) + (637082449068117/25000000000000 : ℝ)*(major2) + (13780172259/100000000000000 : ℝ)*(sp0) + (161942566939/100000000000000 : ℝ)*(sp2) + (543032563/781250000000 : ℝ)*(sp3) + (44240314518917/1250000000000 : ℝ)*(sp8) + (3539238941685619/100000000000000 : ℝ)*(sp9) + (88476924977967/2500000000000 : ℝ)*(sp10) + (382610238679941/25000000000000 : ℝ)*(sp11) + (1530510462887827/100000000000000 : ℝ)*(f.failure) + (3539238941685619/100000000000000 : ℝ)*(f.sum) + (53250686384519/22135000000000000000000000000 : ℝ)*base66 + (1477703075273231517/221350000000000000000000000000000 : ℝ)*base68 + (232351527253568483/221350000000000000000000000000000 : ℝ)*base69 + (485685581830068483/221350000000000000000000000000000 : ℝ)*base71 + (87310139827687/11067500000000000000000000000 : ℝ)*base74 + (1439512322340768483/221350000000000000000000000000000 : ℝ)*base75 + (1485328636032618483/221350000000000000000000000000000 : ℝ)*base77 + (994520083140681517/221350000000000000000000000000000 : ℝ)*base80 + (45362276664089/22135000000000000000000000000 : ℝ)*base82 + (741589/156250000000000000000 : ℝ)*base90 + (741589/156250000000000000000 : ℝ)*base92 + (741589/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-86249/100000 : ℝ) ≤ (-19090608876592680593897767702131/22135000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2929397/100000000000000 : ℝ)*(lower0) + (11992743/25000000000000 : ℝ)*(upper3) + (31122267/50000000000000 : ℝ)*(lower4) + (258833808733023/10000000000000 : ℝ)*(major0) + (258833808733023/10000000000000 : ℝ)*(major1) + (258833808733023/10000000000000 : ℝ)*(major2) + (615200171/100000000000000 : ℝ)*(sp0) + (92444837897/100000000000000 : ℝ)*(sp5) + (8672254679/25000000000000 : ℝ)*(sp7) + (3531749021/100000000000000 : ℝ)*(sp8) + (1825440797529189/50000000000000 : ℝ)*(sp12) + (456349162146209/12500000000000 : ℝ)*(sp13) + (3650885742007569/100000000000000 : ℝ)*(sp14) + (1554504495801309/100000000000000 : ℝ)*(sp15) + (62181567392801/4000000000000 : ℝ)*(f.failure) + (3650885742007569/100000000000000 : ℝ)*(f.sum) + (29153207623603/2213500000000000000000000000 : ℝ)*base65 + (74819872443707623/88540000000000000000000000000000 : ℝ)*base68 + (673293661497852377/88540000000000000000000000000000 : ℝ)*base69 + (1327179040976112377/88540000000000000000000000000000 : ℝ)*base71 + (3454015465021/2213500000000000000000000000 : ℝ)*base73 + (452619345034072377/88540000000000000000000000000000 : ℝ)*base75 + (908902355328232377/88540000000000000000000000000000 : ℝ)*base77 + (733253712358492377/88540000000000000000000000000000 : ℝ)*base79 + (9779078212671/2213500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (43007/6250000000000000000 : ℝ)*base90 + (43007/6250000000000000000 : ℝ)*base92 + (43007/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1551_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63797/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14703/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86249/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1551_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1551_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63797/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14703/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86249/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1551_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63797/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14703/25000 : ℝ) else (10091/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86249/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
