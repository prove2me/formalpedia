-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:19.556593+00:00
-- url     : https://prove2.me/submissions/15ce5cdb-db32-4bc7-be47-ccfee24783de

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
theorem support_rectangle_w1177_s0_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-470195667/2500000000 : ℝ)*x 0 + (1209255169/2000000000 : ℝ)*x 1 + (4784883001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470195667/2500000000 : ℝ)^4185 ≤ (10946164586277/100000000000000 : ℝ)^3161 := by
    have hnat : (470195667 : ℕ)^4185*100000000000000^3161 ≤ 10946164586277^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470195667 2500000000 10946164586277 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209255169/2000000000 : ℝ)^4185 ≤ (25684516578547/50000000000000 : ℝ)^3161 := by
    have hnat : (1209255169 : ℕ)^4185*50000000000000^3161 ≤ 25684516578547^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209255169 2000000000 25684516578547 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4784883001/10000000000 : ℝ)^4185 ≤ (18842401122941/50000000000000 : ℝ)^3161 := by
    have hnat : (4784883001 : ℕ)^4185*50000000000000^3161 ≤ 18842401122941^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784883001 10000000000 18842401122941 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470195667/2500000000 : ℝ), (1209255169/2000000000 : ℝ), (4784883001/10000000000 : ℝ)] ![(10946164586277/100000000000000 : ℝ), (25684516578547/50000000000000 : ℝ), (18842401122941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470195667/2500000000 : ℝ)|^4185 ≤ (10946164586277/100000000000000 : ℝ)^3161
        have hw : |(-470195667/2500000000 : ℝ)|=(470195667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209255169/2000000000 : ℝ)|^4185 ≤ (25684516578547/50000000000000 : ℝ)^3161
        have hw : |(1209255169/2000000000 : ℝ)|=(1209255169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4784883001/10000000000 : ℝ)|^4185 ≤ (18842401122941/50000000000000 : ℝ)^3161
        have hw : |(4784883001/10000000000 : ℝ)|=(4784883001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1102964319/2000000000 : ℝ)*x 0 + (-2603690581/10000000000 : ℝ)*x 1 + (2392441373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102964319/2000000000 : ℝ)^4185 ≤ (45477970221643/100000000000000 : ℝ)^3161 := by
    have hnat : (1102964319 : ℕ)^4185*100000000000000^3161 ≤ 45477970221643^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102964319 2000000000 45477970221643 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603690581/10000000000 : ℝ)^4185 ≤ (16837230179259/100000000000000 : ℝ)^3161 := by
    have hnat : (2603690581 : ℕ)^4185*100000000000000^3161 ≤ 16837230179259^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603690581 10000000000 16837230179259 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2392441373/5000000000 : ℝ)^4185 ≤ (37684799586957/100000000000000 : ℝ)^3161 := by
    have hnat : (2392441373 : ℕ)^4185*100000000000000^3161 ≤ 37684799586957^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392441373 5000000000 37684799586957 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102964319/2000000000 : ℝ), (-2603690581/10000000000 : ℝ), (2392441373/5000000000 : ℝ)] ![(45477970221643/100000000000000 : ℝ), (16837230179259/100000000000000 : ℝ), (37684799586957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102964319/2000000000 : ℝ)|^4185 ≤ (45477970221643/100000000000000 : ℝ)^3161
        have hw : |(1102964319/2000000000 : ℝ)|=(1102964319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2603690581/10000000000 : ℝ)|^4185 ≤ (16837230179259/100000000000000 : ℝ)^3161
        have hw : |(-2603690581/10000000000 : ℝ)|=(2603690581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2392441373/5000000000 : ℝ)|^4185 ≤ (37684799586957/100000000000000 : ℝ)^3161
        have hw : |(2392441373/5000000000 : ℝ)|=(2392441373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5514821977/10000000000 : ℝ)*x 0 + (4784882553/10000000000 : ℝ)*x 1 + (-2603690329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514821977/10000000000 : ℝ)^4185 ≤ (9095594878459/20000000000000 : ℝ)^3161 := by
    have hnat : (5514821977 : ℕ)^4185*20000000000000^3161 ≤ 9095594878459^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514821977 10000000000 9095594878459 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784882553/10000000000 : ℝ)^4185 ≤ (9421199393629/25000000000000 : ℝ)^3161 := by
    have hnat : (4784882553 : ℕ)^4185*25000000000000^3161 ≤ 9421199393629^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784882553 10000000000 9421199393629 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603690329/10000000000 : ℝ)^4185 ≤ (67348912087/400000000000 : ℝ)^3161 := by
    have hnat : (2603690329 : ℕ)^4185*400000000000^3161 ≤ 67348912087^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603690329 10000000000 67348912087 400000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514821977/10000000000 : ℝ), (4784882553/10000000000 : ℝ), (-2603690329/10000000000 : ℝ)] ![(9095594878459/20000000000000 : ℝ), (9421199393629/25000000000000 : ℝ), (67348912087/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514821977/10000000000 : ℝ)|^4185 ≤ (9095594878459/20000000000000 : ℝ)^3161
        have hw : |(5514821977/10000000000 : ℝ)|=(5514821977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784882553/10000000000 : ℝ)|^4185 ≤ (9421199393629/25000000000000 : ℝ)^3161
        have hw : |(4784882553/10000000000 : ℝ)|=(4784882553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2603690329/10000000000 : ℝ)|^4185 ≤ (67348912087/400000000000 : ℝ)^3161
        have hw : |(-2603690329/10000000000 : ℝ)|=(2603690329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2099087459/5000000000 : ℝ)*x 0 + (3119512517/10000000000 : ℝ)*x 1 + (2823130383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099087459/5000000000 : ℝ)^4185 ≤ (7923037407097/25000000000000 : ℝ)^3161 := by
    have hnat : (2099087459 : ℕ)^4185*25000000000000^3161 ≤ 7923037407097^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099087459 5000000000 7923037407097 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119512517/10000000000 : ℝ)^4185 ≤ (4277865024279/20000000000000 : ℝ)^3161 := by
    have hnat : (3119512517 : ℕ)^4185*20000000000000^3161 ≤ 4277865024279^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119512517 10000000000 4277865024279 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823130383/5000000000 : ℝ)^4185 ≤ (2932407827359/6250000000000 : ℝ)^3161 := by
    have hnat : (2823130383 : ℕ)^4185*6250000000000^3161 ≤ 2932407827359^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823130383 5000000000 2932407827359 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099087459/5000000000 : ℝ), (3119512517/10000000000 : ℝ), (2823130383/5000000000 : ℝ)] ![(7923037407097/25000000000000 : ℝ), (4277865024279/20000000000000 : ℝ), (2932407827359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099087459/5000000000 : ℝ)|^4185 ≤ (7923037407097/25000000000000 : ℝ)^3161
        have hw : |(2099087459/5000000000 : ℝ)|=(2099087459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119512517/10000000000 : ℝ)|^4185 ≤ (4277865024279/20000000000000 : ℝ)^3161
        have hw : |(3119512517/10000000000 : ℝ)|=(3119512517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823130383/5000000000 : ℝ)|^4185 ≤ (2932407827359/6250000000000 : ℝ)^3161
        have hw : |(2823130383/5000000000 : ℝ)|=(2823130383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885825989/10000000000 : ℝ)*x 0 + (301087801/625000000 : ℝ)*x 1 + (6012608129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885825989/10000000000 : ℝ)^4185 ≤ (10985042183097/100000000000000 : ℝ)^3161 := by
    have hnat : (1885825989 : ℕ)^4185*100000000000000^3161 ≤ 10985042183097^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885825989 10000000000 10985042183097 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301087801/625000000 : ℝ)^4185 ≤ (38024285051487/100000000000000 : ℝ)^3161 := by
    have hnat : (301087801 : ℕ)^4185*100000000000000^3161 ≤ 38024285051487^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301087801 625000000 38024285051487 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6012608129/10000000000 : ℝ)^4185 ≤ (50990672749273/100000000000000 : ℝ)^3161 := by
    have hnat : (6012608129 : ℕ)^4185*100000000000000^3161 ≤ 50990672749273^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012608129 10000000000 50990672749273 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885825989/10000000000 : ℝ), (301087801/625000000 : ℝ), (6012608129/10000000000 : ℝ)] ![(10985042183097/100000000000000 : ℝ), (38024285051487/100000000000000 : ℝ), (50990672749273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885825989/10000000000 : ℝ)|^4185 ≤ (10985042183097/100000000000000 : ℝ)^3161
        have hw : |(-1885825989/10000000000 : ℝ)|=(1885825989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301087801/625000000 : ℝ)|^4185 ≤ (38024285051487/100000000000000 : ℝ)^3161
        have hw : |(301087801/625000000 : ℝ)|=(301087801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6012608129/10000000000 : ℝ)|^4185 ≤ (50990672749273/100000000000000 : ℝ)^3161
        have hw : |(6012608129/10000000000 : ℝ)|=(6012608129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51719061/100000000 : ℝ)*x 0 + (-687982579/5000000000 : ℝ)*x 1 + (6012607867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51719061/100000000 : ℝ)^4185 ≤ (4177229076489/10000000000000 : ℝ)^3161 := by
    have hnat : (51719061 : ℕ)^4185*10000000000000^3161 ≤ 4177229076489^3161*100000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51719061 100000000 4177229076489 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687982579/5000000000 : ℝ)^4185 ≤ (3618519703859/50000000000000 : ℝ)^3161 := by
    have hnat : (687982579 : ℕ)^4185*50000000000000^3161 ≤ 3618519703859^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687982579 5000000000 3618519703859 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6012607867/10000000000 : ℝ)^4185 ≤ (50990669807561/100000000000000 : ℝ)^3161 := by
    have hnat : (6012607867 : ℕ)^4185*100000000000000^3161 ≤ 50990669807561^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012607867 10000000000 50990669807561 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51719061/100000000 : ℝ), (-687982579/5000000000 : ℝ), (6012607867/10000000000 : ℝ)] ![(4177229076489/10000000000000 : ℝ), (3618519703859/50000000000000 : ℝ), (50990669807561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51719061/100000000 : ℝ)|^4185 ≤ (4177229076489/10000000000000 : ℝ)^3161
        have hw : |(51719061/100000000 : ℝ)|=(51719061/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-687982579/5000000000 : ℝ)|^4185 ≤ (3618519703859/50000000000000 : ℝ)^3161
        have hw : |(-687982579/5000000000 : ℝ)|=(687982579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6012607867/10000000000 : ℝ)|^4185 ≤ (50990669807561/100000000000000 : ℝ)^3161
        have hw : |(6012607867/10000000000 : ℝ)|=(6012607867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585953027/5000000000 : ℝ)*x 0 + (1503151999/2500000000 : ℝ)*x 1 + (-687982511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585953027/5000000000 : ℝ)^4185 ≤ (20886145136501/50000000000000 : ℝ)^3161 := by
    have hnat : (2585953027 : ℕ)^4185*50000000000000^3161 ≤ 20886145136501^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585953027 5000000000 20886145136501 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503151999/2500000000 : ℝ)^4185 ≤ (50990671255961/100000000000000 : ℝ)^3161 := by
    have hnat : (1503151999 : ℕ)^4185*100000000000000^3161 ≤ 50990671255961^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503151999 2500000000 50990671255961 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687982511/5000000000 : ℝ)^4185 ≤ (7237038460689/100000000000000 : ℝ)^3161 := by
    have hnat : (687982511 : ℕ)^4185*100000000000000^3161 ≤ 7237038460689^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687982511 5000000000 7237038460689 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585953027/5000000000 : ℝ), (1503151999/2500000000 : ℝ), (-687982511/5000000000 : ℝ)] ![(20886145136501/50000000000000 : ℝ), (50990671255961/100000000000000 : ℝ), (7237038460689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585953027/5000000000 : ℝ)|^4185 ≤ (20886145136501/50000000000000 : ℝ)^3161
        have hw : |(2585953027/5000000000 : ℝ)|=(2585953027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1503151999/2500000000 : ℝ)|^4185 ≤ (50990671255961/100000000000000 : ℝ)^3161
        have hw : |(1503151999/2500000000 : ℝ)|=(1503151999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-687982511/5000000000 : ℝ)|^4185 ≤ (7237038460689/100000000000000 : ℝ)^3161
        have hw : |(-687982511/5000000000 : ℝ)|=(687982511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s0_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208277629/10000000000 : ℝ)*x 0 + (1395278627/2500000000 : ℝ)*x 1 + (3186954199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208277629/10000000000 : ℝ)^4185 ≤ (31793160756211/100000000000000 : ℝ)^3161 := by
    have hnat : (4208277629 : ℕ)^4185*100000000000000^3161 ≤ 31793160756211^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208277629 10000000000 31793160756211 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395278627/2500000000 : ℝ)^4185 ≤ (57753946879/125000000000 : ℝ)^3161 := by
    have hnat : (1395278627 : ℕ)^4185*125000000000^3161 ≤ 57753946879^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395278627 2500000000 57753946879 125000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186954199/10000000000 : ℝ)^4185 ≤ (22003681727721/100000000000000 : ℝ)^3161 := by
    have hnat : (3186954199 : ℕ)^4185*100000000000000^3161 ≤ 22003681727721^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186954199 10000000000 22003681727721 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208277629/10000000000 : ℝ), (1395278627/2500000000 : ℝ), (3186954199/10000000000 : ℝ)] ![(31793160756211/100000000000000 : ℝ), (57753946879/125000000000 : ℝ), (22003681727721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208277629/10000000000 : ℝ)|^4185 ≤ (31793160756211/100000000000000 : ℝ)^3161
        have hw : |(4208277629/10000000000 : ℝ)|=(4208277629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395278627/2500000000 : ℝ)|^4185 ≤ (57753946879/125000000000 : ℝ)^3161
        have hw : |(1395278627/2500000000 : ℝ)|=(1395278627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186954199/10000000000 : ℝ)|^4185 ≤ (22003681727721/100000000000000 : ℝ)^3161
        have hw : |(3186954199/10000000000 : ℝ)|=(3186954199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (557/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27681/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8369/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8369 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8369*1^2048 ≤ 0^2048*1^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8369/2048 : ℝ) ≤ (36954532726296639/1562500000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8369 ≤ (36954532726296639/1562500000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8369*1562500000000000000^2048 ≤ 36954532726296639^2048*5^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 36954532726296639 1562500000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (36954532726296639/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8369 := by
      have hnat : (1 : ℕ)^2048*1^8369 ≤ 1^8369*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1599454532726296639/1562500000000000000 : ℝ) ≤ (62858542799113/62500000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (1599454532726296639/1562500000000000000 : ℝ)^2048 ≤ (62858542799113/62500000000000 : ℝ)^8369 := by
      have hnat : (1599454532726296639 : ℕ)^2048*62500000000000^8369 ≤ 62858542799113^8369*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1599454532726296639 1562500000000000000 62858542799113 62500000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62858542799113/62500000000000 : ℝ)) (X := (1599454532726296639/1562500000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (818204532726296639/781250000000000000 : ℝ) ≤ (31608542799113/31250000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (818204532726296639/781250000000000000 : ℝ)^2048 ≤ (31608542799113/31250000000000 : ℝ)^8369 := by
      have hnat : (818204532726296639 : ℕ)^2048*31250000000000^8369 ≤ 31608542799113^8369*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        818204532726296639 781250000000000000 31608542799113 31250000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31608542799113/31250000000000 : ℝ)) (X := (818204532726296639/781250000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(358542799113/25000000000000 : ℝ)*(0 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(358542799113/25000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36954532726296639/1562500000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(358542799113/25000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (1 : ℝ)+(358542799113/25000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(62858542799113/62500000000000 : ℝ) by norm_num, show 1+(36954532726296639/1562500000000000000 : ℝ)+(0 : ℝ)=(1599454532726296639/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36954532726296639/1562500000000000000 : ℝ) ≤ ((1 : ℝ)+2*(358542799113/25000000000000 : ℝ)*(2/5 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(358542799113/25000000000000 : ℝ)*(2/5 : ℝ)=(31608542799113/31250000000000 : ℝ) by norm_num, show 1+2*(36954532726296639/1562500000000000000 : ℝ)=(818204532726296639/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(358542799113/25000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (358542799113/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(358542799113/25000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (358542799113/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(358542799113/25000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (358542799113/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-470195667/2500000000 : ℝ)*X 0 0+(1209255169/2000000000 : ℝ)*X 0 1+(4784883001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1102964319/2000000000 : ℝ)*X 1 0+(-2603690581/10000000000 : ℝ)*X 1 1+(2392441373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5514821977/10000000000 : ℝ)*X 2 0+(4784882553/10000000000 : ℝ)*X 2 1+(-2603690329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099087459/5000000000 : ℝ)*X 0 0+(3119512517/10000000000 : ℝ)*X 0 1+(2823130383/5000000000 : ℝ)*X 0 2+(2099087459/5000000000 : ℝ)*X 1 0+(3119512517/10000000000 : ℝ)*X 1 1+(2823130383/5000000000 : ℝ)*X 1 2+(2099087459/5000000000 : ℝ)*X 2 0+(3119512517/10000000000 : ℝ)*X 2 1+(2823130383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1885825989/10000000000 : ℝ)*X 0 0+(301087801/625000000 : ℝ)*X 0 1+(6012608129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((51719061/100000000 : ℝ)*X 1 0+(-687982579/5000000000 : ℝ)*X 1 1+(6012607867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585953027/5000000000 : ℝ)*X 2 0+(1503151999/2500000000 : ℝ)*X 2 1+(-687982511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208277629/10000000000 : ℝ)*X 0 0+(1395278627/2500000000 : ℝ)*X 0 1+(3186954199/10000000000 : ℝ)*X 0 2+(4208277629/10000000000 : ℝ)*X 1 0+(1395278627/2500000000 : ℝ)*X 1 1+(3186954199/10000000000 : ℝ)*X 1 2+(4208277629/10000000000 : ℝ)*X 2 0+(1395278627/2500000000 : ℝ)*X 2 1+(3186954199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1663933831338020768883/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163621/781250000000 : ℝ)*(base1) + (642796867/100000000000000 : ℝ)*(base19) + (156634067/25000000000000 : ℝ)*(base23) + (7117457/10000000000000 : ℝ)*(base24) + (157892631/100000000000000 : ℝ)*(upper3) + (594272430460597/100000000000000 : ℝ)*(major0) + (594272430460597/100000000000000 : ℝ)*(major1) + (594272430460597/100000000000000 : ℝ)*(major2) + (99097045511371/12500000000000 : ℝ)*(sp0) + (792776898472467/100000000000000 : ℝ)*(sp1) + (24774276361203/3125000000000 : ℝ)*(sp2) + (197883064967437/50000000000000 : ℝ)*(sp3) + (599060927/50000000000000 : ℝ)*(sp4) + (270007589/25000000000000 : ℝ)*(sp7) + (197883615454359/50000000000000 : ℝ)*(f.failure) + (396388770634667/50000000000000 : ℝ)*(f.sum) + (161995517961/1250000000000000000000000000 : ℝ)*base65 + (15921115774539/2500000000000000000000000000 : ℝ)*base68 + (6399778104539/2500000000000000000000000000 : ℝ)*base70 + (12709069752039/2500000000000000000000000000 : ℝ)*base72 + (1624621326711/1250000000000000000000000000 : ℝ)*base73 + (12926198724539/2500000000000000000000000000 : ℝ)*base76 + (15462424069539/2500000000000000000000000000 : ℝ)*base78 + (23745624434539/2500000000000000000000000000 : ℝ)*base80 + (1060308379539/1250000000000000000000000000 : ℝ)*base82 + (15357911/2500000000000000000000 : ℝ)*base89 + (15357911/2500000000000000000000 : ℝ)*base91 + (15357911/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148928865081778225629/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (6882603/25000000000000 : ℝ)*(base1) + (248587807/50000000000000 : ℝ)*(base19) + (12288437/2500000000000 : ℝ)*(base23) + (2206303/5000000000000 : ℝ)*(upper3) + (12981711/20000000000000 : ℝ)*(upper5) + (627180423271681/100000000000000 : ℝ)*(major0) + (627180423271681/100000000000000 : ℝ)*(major1) + (627180423271681/100000000000000 : ℝ)*(major2) + (235483159/25000000000000 : ℝ)*(sp1) + (96913131/10000000000000 : ℝ)*(sp2) + (418338932335203/50000000000000 : ℝ)*(sp4) + (6536534359623/781250000000 : ℝ)*(sp5) + (209169094117801/25000000000000 : ℝ)*(sp6) + (26105182395623/6250000000000 : ℝ)*(sp7) + (417682945860381/100000000000000 : ℝ)*(f.failure) + (418338918569997/50000000000000 : ℝ)*(f.sum) + (2355124396453/1250000000000000000000000000 : ℝ)*base65 + (20498377218953/2500000000000000000000000000 : ℝ)*base67 + (3114839803953/2500000000000000000000000000 : ℝ)*base69 + (16606008088953/2500000000000000000000000000 : ℝ)*base71 + (2475631473953/1250000000000000000000000000 : ℝ)*base73 + (2716094478953/2500000000000000000000000000 : ℝ)*base75 + (8416617923953/2500000000000000000000000000 : ℝ)*base77 + (10243111423953/2500000000000000000000000000 : ℝ)*base79 + (2510005373547/1250000000000000000000000000 : ℝ)*base82 + (5140451/5000000000000000000000 : ℝ)*base90 + (5140451/5000000000000000000000 : ℝ)*base92 + (5140451/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1177_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s1_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082916823/10000000000 : ℝ)*x 0 + (2846121391/5000000000 : ℝ)*x 1 + (1001904189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082916823/10000000000 : ℝ)^4185 ≤ (12530170515057/100000000000000 : ℝ)^3161 := by
    have hnat : (2082916823 : ℕ)^4185*100000000000000^3161 ≤ 12530170515057^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082916823 10000000000 12530170515057 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2846121391/5000000000 : ℝ)^4185 ≤ (47425065350751/100000000000000 : ℝ)^3161 := by
    have hnat : (2846121391 : ℕ)^4185*100000000000000^3161 ≤ 47425065350751^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846121391 5000000000 47425065350751 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001904189/2000000000 : ℝ)^4185 ≤ (40044764113281/100000000000000 : ℝ)^3161 := by
    have hnat : (1001904189 : ℕ)^4185*100000000000000^3161 ≤ 40044764113281^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001904189 2000000000 40044764113281 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082916823/10000000000 : ℝ), (2846121391/5000000000 : ℝ), (1001904189/2000000000 : ℝ)] ![(12530170515057/100000000000000 : ℝ), (47425065350751/100000000000000 : ℝ), (40044764113281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082916823/10000000000 : ℝ)|^4185 ≤ (12530170515057/100000000000000 : ℝ)^3161
        have hw : |(-2082916823/10000000000 : ℝ)|=(2082916823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2846121391/5000000000 : ℝ)|^4185 ≤ (47425065350751/100000000000000 : ℝ)^3161
        have hw : |(2846121391/5000000000 : ℝ)|=(2846121391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001904189/2000000000 : ℝ)|^4185 ≤ (40044764113281/100000000000000 : ℝ)^3161
        have hw : |(1001904189/2000000000 : ℝ)|=(1001904189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216688013/400000000 : ℝ)*x 0 + (-245070007/1000000000 : ℝ)*x 1 + (5009519999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216688013/400000000 : ℝ)^4185 ≤ (11103803896901/25000000000000 : ℝ)^3161 := by
    have hnat : (216688013 : ℕ)^4185*25000000000000^3161 ≤ 11103803896901^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216688013 400000000 11103803896901 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245070007/1000000000 : ℝ)^4185 ≤ (1942503786793/12500000000000 : ℝ)^3161 := by
    have hnat : (245070007 : ℕ)^4185*12500000000000^3161 ≤ 1942503786793^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245070007 1000000000 1942503786793 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5009519999/10000000000 : ℝ)^4185 ≤ (40044754101493/100000000000000 : ℝ)^3161 := by
    have hnat : (5009519999 : ℕ)^4185*100000000000000^3161 ≤ 40044754101493^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009519999 10000000000 40044754101493 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216688013/400000000 : ℝ), (-245070007/1000000000 : ℝ), (5009519999/10000000000 : ℝ)] ![(11103803896901/25000000000000 : ℝ), (1942503786793/12500000000000 : ℝ), (40044754101493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216688013/400000000 : ℝ)|^4185 ≤ (11103803896901/25000000000000 : ℝ)^3161
        have hw : |(216688013/400000000 : ℝ)|=(216688013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245070007/1000000000 : ℝ)|^4185 ≤ (1942503786793/12500000000000 : ℝ)^3161
        have hw : |(-245070007/1000000000 : ℝ)|=(245070007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5009519999/10000000000 : ℝ)|^4185 ≤ (40044754101493/100000000000000 : ℝ)^3161
        have hw : |(5009519999/10000000000 : ℝ)|=(5009519999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708601211/5000000000 : ℝ)*x 0 + (5009518011/10000000000 : ℝ)*x 1 + (-306337483/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708601211/5000000000 : ℝ)^4185 ≤ (11103809587609/25000000000000 : ℝ)^3161 := by
    have hnat : (2708601211 : ℕ)^4185*25000000000000^3161 ≤ 11103809587609^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708601211 5000000000 11103809587609 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5009518011/10000000000 : ℝ)^4185 ≤ (10011183265481/25000000000000 : ℝ)^3161 := by
    have hnat : (5009518011 : ℕ)^4185*25000000000000^3161 ≤ 10011183265481^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009518011 10000000000 10011183265481 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306337483/1250000000 : ℝ)^4185 ≤ (15540028564927/100000000000000 : ℝ)^3161 := by
    have hnat : (306337483 : ℕ)^4185*100000000000000^3161 ≤ 15540028564927^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306337483 1250000000 15540028564927 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708601211/5000000000 : ℝ), (5009518011/10000000000 : ℝ), (-306337483/1250000000 : ℝ)] ![(11103809587609/25000000000000 : ℝ), (10011183265481/25000000000000 : ℝ), (15540028564927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708601211/5000000000 : ℝ)|^4185 ≤ (11103809587609/25000000000000 : ℝ)^3161
        have hw : |(2708601211/5000000000 : ℝ)|=(2708601211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5009518011/10000000000 : ℝ)|^4185 ≤ (10011183265481/25000000000000 : ℝ)^3161
        have hw : |(5009518011/10000000000 : ℝ)|=(5009518011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-306337483/1250000000 : ℝ)|^4185 ≤ (15540028564927/100000000000000 : ℝ)^3161
        have hw : |(-306337483/1250000000 : ℝ)|=(306337483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157232329/5000000000 : ℝ)*x 0 + (736718387/2000000000 : ℝ)*x 1 + (1262793589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157232329/5000000000 : ℝ)^4185 ≤ (32859592805027/100000000000000 : ℝ)^3161 := by
    have hnat : (2157232329 : ℕ)^4185*100000000000000^3161 ≤ 32859592805027^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157232329 5000000000 32859592805027 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736718387/2000000000 : ℝ)^4185 ≤ (26654220529543/100000000000000 : ℝ)^3161 := by
    have hnat : (736718387 : ℕ)^4185*100000000000000^3161 ≤ 26654220529543^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736718387 2000000000 26654220529543 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262793589/2500000000 : ℝ)^4185 ≤ (5060773331009/12500000000000 : ℝ)^3161 := by
    have hnat : (1262793589 : ℕ)^4185*12500000000000^3161 ≤ 5060773331009^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262793589 2500000000 5060773331009 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157232329/5000000000 : ℝ), (736718387/2000000000 : ℝ), (1262793589/2500000000 : ℝ)] ![(32859592805027/100000000000000 : ℝ), (26654220529543/100000000000000 : ℝ), (5060773331009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157232329/5000000000 : ℝ)|^4185 ≤ (32859592805027/100000000000000 : ℝ)^3161
        have hw : |(2157232329/5000000000 : ℝ)|=(2157232329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736718387/2000000000 : ℝ)|^4185 ≤ (26654220529543/100000000000000 : ℝ)^3161
        have hw : |(736718387/2000000000 : ℝ)|=(736718387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1262793589/2500000000 : ℝ)|^4185 ≤ (5060773331009/12500000000000 : ℝ)^3161
        have hw : |(1262793589/2500000000 : ℝ)|=(1262793589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083678813/10000000000 : ℝ)*x 0 + (1254679609/2500000000 : ℝ)*x 1 + (22198683/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083678813/10000000000 : ℝ)^4185 ≤ (125362397091/1000000000000 : ℝ)^3161 := by
    have hnat : (2083678813 : ℕ)^4185*1000000000000^3161 ≤ 125362397091^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083678813 10000000000 125362397091 1000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1254679609/2500000000 : ℝ)^4185 ≤ (20071066360607/50000000000000 : ℝ)^3161 := by
    have hnat : (1254679609 : ℕ)^4185*50000000000000^3161 ≤ 20071066360607^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254679609 2500000000 20071066360607 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22198683/39062500 : ℝ)^4185 ≤ (47321627545591/100000000000000 : ℝ)^3161 := by
    have hnat : (22198683 : ℕ)^4185*100000000000000^3161 ≤ 47321627545591^3161*39062500^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22198683 39062500 47321627545591 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083678813/10000000000 : ℝ), (1254679609/2500000000 : ℝ), (22198683/39062500 : ℝ)] ![(125362397091/1000000000000 : ℝ), (20071066360607/50000000000000 : ℝ), (47321627545591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083678813/10000000000 : ℝ)|^4185 ≤ (125362397091/1000000000000 : ℝ)^3161
        have hw : |(-2083678813/10000000000 : ℝ)|=(2083678813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1254679609/2500000000 : ℝ)|^4185 ≤ (20071066360607/50000000000000 : ℝ)^3161
        have hw : |(1254679609/2500000000 : ℝ)|=(1254679609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22198683/39062500 : ℝ)|^4185 ≤ (47321627545591/100000000000000 : ℝ)^3161
        have hw : |(22198683/39062500 : ℝ)|=(22198683/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5241858869/10000000000 : ℝ)*x 0 + (-1777354883/10000000000 : ℝ)*x 1 + (5682865107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241858869/10000000000 : ℝ)^4185 ≤ (42521945114981/100000000000000 : ℝ)^3161 := by
    have hnat : (5241858869 : ℕ)^4185*100000000000000^3161 ≤ 42521945114981^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241858869 10000000000 42521945114981 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777354883/10000000000 : ℝ)^4185 ≤ (10156402420053/100000000000000 : ℝ)^3161 := by
    have hnat : (1777354883 : ℕ)^4185*100000000000000^3161 ≤ 10156402420053^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777354883 10000000000 10156402420053 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682865107/10000000000 : ℝ)^4185 ≤ (47321652450199/100000000000000 : ℝ)^3161 := by
    have hnat : (5682865107 : ℕ)^4185*100000000000000^3161 ≤ 47321652450199^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682865107 10000000000 47321652450199 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241858869/10000000000 : ℝ), (-1777354883/10000000000 : ℝ), (5682865107/10000000000 : ℝ)] ![(42521945114981/100000000000000 : ℝ), (10156402420053/100000000000000 : ℝ), (47321652450199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241858869/10000000000 : ℝ)|^4185 ≤ (42521945114981/100000000000000 : ℝ)^3161
        have hw : |(5241858869/10000000000 : ℝ)|=(5241858869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777354883/10000000000 : ℝ)|^4185 ≤ (10156402420053/100000000000000 : ℝ)^3161
        have hw : |(-1777354883/10000000000 : ℝ)|=(1777354883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682865107/10000000000 : ℝ)|^4185 ≤ (47321652450199/100000000000000 : ℝ)^3161
        have hw : |(5682865107/10000000000 : ℝ)|=(5682865107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2620929189/5000000000 : ℝ)*x 0 + (2841433079/5000000000 : ℝ)*x 1 + (-27771157/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620929189/5000000000 : ℝ)^4185 ≤ (10630484960427/25000000000000 : ℝ)^3161 := by
    have hnat : (2620929189 : ℕ)^4185*25000000000000^3161 ≤ 10630484960427^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620929189 5000000000 10630484960427 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841433079/5000000000 : ℝ)^4185 ≤ (2957604002317/6250000000000 : ℝ)^3161 := by
    have hnat : (2841433079 : ℕ)^4185*6250000000000^3161 ≤ 2957604002317^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841433079 5000000000 2957604002317 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27771157/156250000 : ℝ)^4185 ≤ (81251168823/800000000000 : ℝ)^3161 := by
    have hnat : (27771157 : ℕ)^4185*800000000000^3161 ≤ 81251168823^3161*156250000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27771157 156250000 81251168823 800000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620929189/5000000000 : ℝ), (2841433079/5000000000 : ℝ), (-27771157/156250000 : ℝ)] ![(10630484960427/25000000000000 : ℝ), (2957604002317/6250000000000 : ℝ), (81251168823/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620929189/5000000000 : ℝ)|^4185 ≤ (10630484960427/25000000000000 : ℝ)^3161
        have hw : |(2620929189/5000000000 : ℝ)|=(2620929189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2841433079/5000000000 : ℝ)|^4185 ≤ (2957604002317/6250000000000 : ℝ)^3161
        have hw : |(2841433079/5000000000 : ℝ)|=(2841433079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27771157/156250000 : ℝ)|^4185 ≤ (81251168823/800000000000 : ℝ)^3161
        have hw : |(-27771157/156250000 : ℝ)|=(27771157/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s1_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315979721/10000000000 : ℝ)*x 0 + (2516376979/5000000000 : ℝ)*x 1 + (115699181/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315979721/10000000000 : ℝ)^4185 ≤ (4109358829143/12500000000000 : ℝ)^3161 := by
    have hnat : (4315979721 : ℕ)^4185*12500000000000^3161 ≤ 4109358829143^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315979721 10000000000 4109358829143 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516376979/5000000000 : ℝ)^4185 ≤ (40290830234723/100000000000000 : ℝ)^3161 := by
    have hnat : (2516376979 : ℕ)^4185*100000000000000^3161 ≤ 40290830234723^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516376979 5000000000 40290830234723 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115699181/312500000 : ℝ)^4185 ≤ (5366859823933/20000000000000 : ℝ)^3161 := by
    have hnat : (115699181 : ℕ)^4185*20000000000000^3161 ≤ 5366859823933^3161*312500000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115699181 312500000 5366859823933 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315979721/10000000000 : ℝ), (2516376979/5000000000 : ℝ), (115699181/312500000 : ℝ)] ![(4109358829143/12500000000000 : ℝ), (40290830234723/100000000000000 : ℝ), (5366859823933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315979721/10000000000 : ℝ)|^4185 ≤ (4109358829143/12500000000000 : ℝ)^3161
        have hw : |(4315979721/10000000000 : ℝ)|=(4315979721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516376979/5000000000 : ℝ)|^4185 ≤ (40290830234723/100000000000000 : ℝ)^3161
        have hw : |(2516376979/5000000000 : ℝ)|=(2516376979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115699181/312500000 : ℝ)|^4185 ≤ (5366859823933/20000000000000 : ℝ)^3161
        have hw : |(115699181/312500000 : ℝ)|=(115699181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (507/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (557/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (557/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (557/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (557/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (557/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (557/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (557/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (384135613/625000000000000000 : ℝ) := by
    have hpowers : (557/100000 : ℝ)^8369 ≤ (384135613/625000000000000000 : ℝ)^2048 := by
      have hnat : (557 : ℕ)^8369*625000000000000000^2048 ≤ 384135613^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        557 100000 384135613 625000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (557/100000 : ℝ)) (X := (384135613/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27681/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (525432854987168433/100000000000000000000 : ℝ) := by
    have hpowers : (27681/100000 : ℝ)^8369 ≤ (525432854987168433/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27681 : ℕ)^8369*100000000000000000000^2048 ≤ 525432854987168433^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27681 100000 525432854987168433 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27681/100000 : ℝ)) (X := (525432854987168433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (312500000384135613/312500000000000000 : ℝ) ≤ (10000000003008091/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (312500000384135613/312500000000000000 : ℝ)^2048 ≤ (10000000003008091/10000000000000000 : ℝ)^8369 := by
      have hnat : (312500000384135613 : ℕ)^2048*10000000000000000^8369 ≤ 10000000003008091^8369*312500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312500000384135613 312500000000000000 10000000003008091 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000003008091/10000000000000000 : ℝ)) (X := (312500000384135613/312500000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100525432916448866513/100000000000000000000 : ℝ) ≤ (5006416285777207/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (100525432916448866513/100000000000000000000 : ℝ)^2048 ≤ (5006416285777207/5000000000000000 : ℝ)^8369 := by
      have hnat : (100525432916448866513 : ℕ)^2048*5000000000000000^8369 ≤ 5006416285777207^8369*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100525432916448866513 100000000000000000000 5006416285777207 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006416285777207/5000000000000000 : ℝ)) (X := (100525432916448866513/100000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50525432854987168433/50000000000000000000 : ℝ) ≤ (10025665140100737/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50525432854987168433/50000000000000000000 : ℝ)^2048 ≤ (10025665140100737/10000000000000000 : ℝ)^8369 := by
      have hnat : (50525432854987168433 : ℕ)^2048*10000000000000000^8369 ≤ 10025665140100737^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50525432854987168433 50000000000000000000 10025665140100737 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025665140100737/10000000000000000 : ℝ)) (X := (50525432854987168433/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(384135613/625000000000000000 : ℝ) ≤ ((135612852300115428231/135620000000000000000 : ℝ)+2*(12832568546323/2712400000000000 : ℝ)*(557/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (135612852300115428231/135620000000000000000 : ℝ)+2*(12832568546323/2712400000000000 : ℝ)*(557/100000 : ℝ)=(10000000003008091/10000000000000000 : ℝ) by norm_num, show 1+2*(384135613/625000000000000000 : ℝ)=(312500000384135613/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(525432854987168433/100000000000000000000 : ℝ)+(384135613/625000000000000000 : ℝ) ≤ ((135612852300115428231/135620000000000000000 : ℝ)+(12832568546323/2712400000000000 : ℝ)*((27681/100000 : ℝ)+(557/100000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (135612852300115428231/135620000000000000000 : ℝ)+(12832568546323/2712400000000000 : ℝ)*((27681/100000 : ℝ)+(557/100000 : ℝ))=(5006416285777207/5000000000000000 : ℝ) by norm_num, show 1+(525432854987168433/100000000000000000000 : ℝ)+(384135613/625000000000000000 : ℝ)=(100525432916448866513/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(525432854987168433/100000000000000000000 : ℝ) ≤ ((135612852300115428231/135620000000000000000 : ℝ)+2*(12832568546323/2712400000000000 : ℝ)*(27681/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (135612852300115428231/135620000000000000000 : ℝ)+2*(12832568546323/2712400000000000 : ℝ)*(27681/100000 : ℝ)=(10025665140100737/10000000000000000 : ℝ) by norm_num, show 1+2*(525432854987168433/100000000000000000000 : ℝ)=(50525432854987168433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (135612852300115428231/135620000000000000000 : ℝ)*(X 1 0+X 2 0)+(12832568546323/2712400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (557/100000 : ℝ)) (hi := (27681/100000 : ℝ)) (c := (135612852300115428231/135620000000000000000 : ℝ)) (alpha := (12832568546323/2712400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (135612852300115428231/135620000000000000000 : ℝ)*(X 0 1+X 2 1)+(12832568546323/2712400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (557/100000 : ℝ)) (hi := (27681/100000 : ℝ)) (c := (135612852300115428231/135620000000000000000 : ℝ)) (alpha := (12832568546323/2712400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (135612852300115428231/135620000000000000000 : ℝ)*(X 0 2+X 1 2)+(12832568546323/2712400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (557/100000 : ℝ)) (hi := (27681/100000 : ℝ)) (c := (135612852300115428231/135620000000000000000 : ℝ)) (alpha := (12832568546323/2712400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2082916823/10000000000 : ℝ)*X 0 0+(2846121391/5000000000 : ℝ)*X 0 1+(1001904189/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((216688013/400000000 : ℝ)*X 1 0+(-245070007/1000000000 : ℝ)*X 1 1+(5009519999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708601211/5000000000 : ℝ)*X 2 0+(5009518011/10000000000 : ℝ)*X 2 1+(-306337483/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157232329/5000000000 : ℝ)*X 0 0+(736718387/2000000000 : ℝ)*X 0 1+(1262793589/2500000000 : ℝ)*X 0 2+(2157232329/5000000000 : ℝ)*X 1 0+(736718387/2000000000 : ℝ)*X 1 1+(1262793589/2500000000 : ℝ)*X 1 2+(2157232329/5000000000 : ℝ)*X 2 0+(736718387/2000000000 : ℝ)*X 2 1+(1262793589/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083678813/10000000000 : ℝ)*X 0 0+(1254679609/2500000000 : ℝ)*X 0 1+(22198683/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241858869/10000000000 : ℝ)*X 1 0+(-1777354883/10000000000 : ℝ)*X 1 1+(5682865107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620929189/5000000000 : ℝ)*X 2 0+(2841433079/5000000000 : ℝ)*X 2 1+(-27771157/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315979721/10000000000 : ℝ)*X 0 0+(2516376979/5000000000 : ℝ)*X 0 1+(115699181/312500000 : ℝ)*X 0 2+(4315979721/10000000000 : ℝ)*X 1 0+(2516376979/5000000000 : ℝ)*X 1 1+(115699181/312500000 : ℝ)*X 1 2+(4315979721/10000000000 : ℝ)*X 2 0+(2516376979/5000000000 : ℝ)*X 2 1+(115699181/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1060741695608461262941161/135620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (868946577/100000000000000 : ℝ)*(base1) + (1443110949/100000000000000 : ℝ)*(base19) + (1042833431/50000000000000 : ℝ)*(base23) + (21443257/25000000000000 : ℝ)*(base37) + (67237567/50000000000000 : ℝ)*(upper3) + (1097973148058169/100000000000000 : ℝ)*(major0) + (1097973148058169/100000000000000 : ℝ)*(major1) + (1097973148058169/100000000000000 : ℝ)*(major2) + (732363958992409/50000000000000 : ℝ)*(sp0) + (1464725781814509/100000000000000 : ℝ)*(sp1) + (146472747367849/10000000000000 : ℝ)*(sp2) + (365607760668599/50000000000000 : ℝ)*(sp3) + (2510307111/100000000000000 : ℝ)*(sp4) + (2334419893/100000000000000 : ℝ)*(sp5) + (365608238028401/50000000000000 : ℝ)*(f.failure) + (183091194918169/12500000000000 : ℝ)*(f.sum) + (95401488604847/135620000000000000000000000000 : ℝ)*base65 + (48773267390861880961/13562000000000000000000000000000000 : ℝ)*base68 + (58470632059149880961/13562000000000000000000000000000000 : ℝ)*base70 + (56715162134650119039/13562000000000000000000000000000000 : ℝ)*base71 + (250711486260633/135620000000000000000000000000 : ℝ)*base74 + (46972373174802119039/13562000000000000000000000000000000 : ℝ)*base75 + (57519302778694119039/13562000000000000000000000000000000 : ℝ)*base77 + (19406130465577880961/13562000000000000000000000000000000 : ℝ)*base80 + (400527394076773/135620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17697871/2500000000000000000000 : ℝ)*base90 + (17697871/2500000000000000000000 : ℝ)*base92 + (17697871/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497987936543360136603656229/339050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1519246863/100000000000000 : ℝ)*(base19) + (263484009/12500000000000 : ℝ)*(base23) + (143056551/50000000000000 : ℝ)*(upper2) + (420928467/100000000000000 : ℝ)*(upper3) + (176747899/100000000000000 : ℝ)*(upper5) + (56433949752447/5000000000000 : ℝ)*(major0) + (56433949752447/5000000000000 : ℝ)*(major1) + (56433949752447/5000000000000 : ℝ)*(major2) + (4270371793/50000000000000 : ℝ)*(sp1) + (14036402347/100000000000000 : ℝ)*(sp2) + (376423077943887/25000000000000 : ℝ)*(sp4) + (1505682251785099/100000000000000 : ℝ)*(sp5) + (1505676167501129/100000000000000 : ℝ)*(sp6) + (751665629363183/100000000000000 : ℝ)*(sp7) + (751665629363183/100000000000000 : ℝ)*(f.failure) + (376423077943887/25000000000000 : ℝ)*(f.sum) + (12798062827071/3390500000000000000000000000 : ℝ)*base65 + (1649966452236018743/678100000000000000000000000000000 : ℝ)*base68 + (2380924814980181257/678100000000000000000000000000000 : ℝ)*base69 + (850432918449781257/678100000000000000000000000000000 : ℝ)*base71 + (1794521168139/1695250000000000000000000000 : ℝ)*base74 + (6908207723915881257/678100000000000000000000000000000 : ℝ)*base75 + (5860279988208281257/678100000000000000000000000000000 : ℝ)*base77 + (1459055040101118743/678100000000000000000000000000000 : ℝ)*base80 + (126983063473/1356200000000000000000000000 : ℝ)*base81 + (13602193/5000000000000000000000 : ℝ)*base90 + (13602193/5000000000000000000000 : ℝ)*base92 + (13602193/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (507/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s2_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134290693/10000000000 : ℝ)*x 0 + (2752134883/5000000000 : ℝ)*x 1 + (322799513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134290693/10000000000 : ℝ)^4185 ≤ (12940960967631/100000000000000 : ℝ)^3161 := by
    have hnat : (2134290693 : ℕ)^4185*100000000000000^3161 ≤ 12940960967631^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134290693 10000000000 12940960967631 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752134883/5000000000 : ℝ)^4185 ≤ (45362801739427/100000000000000 : ℝ)^3161 := by
    have hnat : (2752134883 : ℕ)^4185*100000000000000^3161 ≤ 45362801739427^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752134883 5000000000 45362801739427 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322799513/625000000 : ℝ)^4185 ≤ (10424059320983/25000000000000 : ℝ)^3161 := by
    have hnat : (322799513 : ℕ)^4185*25000000000000^3161 ≤ 10424059320983^3161*625000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322799513 625000000 10424059320983 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134290693/10000000000 : ℝ), (2752134883/5000000000 : ℝ), (322799513/625000000 : ℝ)] ![(12940960967631/100000000000000 : ℝ), (45362801739427/100000000000000 : ℝ), (10424059320983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134290693/10000000000 : ℝ)|^4185 ≤ (12940960967631/100000000000000 : ℝ)^3161
        have hw : |(-2134290693/10000000000 : ℝ)|=(2134290693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752134883/5000000000 : ℝ)|^4185 ≤ (45362801739427/100000000000000 : ℝ)^3161
        have hw : |(2752134883/5000000000 : ℝ)|=(2752134883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322799513/625000000 : ℝ)|^4185 ≤ (10424059320983/25000000000000 : ℝ)^3161
        have hw : |(322799513/625000000 : ℝ)|=(322799513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372372313/10000000000 : ℝ)*x 0 + (-2310548093/10000000000 : ℝ)*x 1 + (5164795441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372372313/10000000000 : ℝ)^4185 ≤ (43929263184241/100000000000000 : ℝ)^3161 := by
    have hnat : (5372372313 : ℕ)^4185*100000000000000^3161 ≤ 43929263184241^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372372313 10000000000 43929263184241 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2310548093/10000000000 : ℝ)^4185 ≤ (2874892992413/20000000000000 : ℝ)^3161 := by
    have hnat : (2310548093 : ℕ)^4185*20000000000000^3161 ≤ 2874892992413^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310548093 10000000000 2874892992413 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5164795441/10000000000 : ℝ)^4185 ≤ (20848135919857/50000000000000 : ℝ)^3161 := by
    have hnat : (5164795441 : ℕ)^4185*50000000000000^3161 ≤ 20848135919857^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164795441 10000000000 20848135919857 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372372313/10000000000 : ℝ), (-2310548093/10000000000 : ℝ), (5164795441/10000000000 : ℝ)] ![(43929263184241/100000000000000 : ℝ), (2874892992413/20000000000000 : ℝ), (20848135919857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372372313/10000000000 : ℝ)|^4185 ≤ (43929263184241/100000000000000 : ℝ)^3161
        have hw : |(5372372313/10000000000 : ℝ)|=(5372372313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2310548093/10000000000 : ℝ)|^4185 ≤ (2874892992413/20000000000000 : ℝ)^3161
        have hw : |(-2310548093/10000000000 : ℝ)|=(2310548093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5164795441/10000000000 : ℝ)|^4185 ≤ (20848135919857/50000000000000 : ℝ)^3161
        have hw : |(5164795441/10000000000 : ℝ)|=(5164795441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074474649/2000000000 : ℝ)*x 0 + (129119851/250000000 : ℝ)*x 1 + (-1155274343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074474649/2000000000 : ℝ)^4185 ≤ (43929273273859/100000000000000 : ℝ)^3161 := by
    have hnat : (1074474649 : ℕ)^4185*100000000000000^3161 ≤ 43929273273859^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074474649 2000000000 43929273273859 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129119851/250000000 : ℝ)^4185 ≤ (8339251373037/20000000000000 : ℝ)^3161 := by
    have hnat : (129119851 : ℕ)^4185*20000000000000^3161 ≤ 8339251373037^3161*250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129119851 250000000 8339251373037 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155274343/5000000000 : ℝ)^4185 ≤ (2874893969273/20000000000000 : ℝ)^3161 := by
    have hnat : (1155274343 : ℕ)^4185*20000000000000^3161 ≤ 2874893969273^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155274343 5000000000 2874893969273 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074474649/2000000000 : ℝ), (129119851/250000000 : ℝ), (-1155274343/5000000000 : ℝ)] ![(43929273273859/100000000000000 : ℝ), (8339251373037/20000000000000 : ℝ), (2874893969273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074474649/2000000000 : ℝ)|^4185 ≤ (43929273273859/100000000000000 : ℝ)^3161
        have hw : |(1074474649/2000000000 : ℝ)|=(1074474649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129119851/250000000 : ℝ)|^4185 ≤ (8339251373037/20000000000000 : ℝ)^3161
        have hw : |(129119851/250000000 : ℝ)|=(129119851/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1155274343/5000000000 : ℝ)|^4185 ≤ (2874893969273/20000000000000 : ℝ)^3161
        have hw : |(-1155274343/5000000000 : ℝ)|=(1155274343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349790513/10000000000 : ℝ)*x 0 + (100571143/250000000 : ℝ)*x 1 + (4702862607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349790513/10000000000 : ℝ)^4185 ≤ (33216268433389/100000000000000 : ℝ)^3161 := by
    have hnat : (4349790513 : ℕ)^4185*100000000000000^3161 ≤ 33216268433389^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349790513 10000000000 33216268433389 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100571143/250000000 : ℝ)^4185 ≤ (3743973121789/12500000000000 : ℝ)^3161 := by
    have hnat : (100571143 : ℕ)^4185*12500000000000^3161 ≤ 3743973121789^3161*250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100571143 250000000 3743973121789 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4702862607/10000000000 : ℝ)^4185 ≤ (36831946578937/100000000000000 : ℝ)^3161 := by
    have hnat : (4702862607 : ℕ)^4185*100000000000000^3161 ≤ 36831946578937^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702862607 10000000000 36831946578937 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349790513/10000000000 : ℝ), (100571143/250000000 : ℝ), (4702862607/10000000000 : ℝ)] ![(33216268433389/100000000000000 : ℝ), (3743973121789/12500000000000 : ℝ), (36831946578937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349790513/10000000000 : ℝ)|^4185 ≤ (33216268433389/100000000000000 : ℝ)^3161
        have hw : |(4349790513/10000000000 : ℝ)|=(4349790513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100571143/250000000 : ℝ)|^4185 ≤ (3743973121789/12500000000000 : ℝ)^3161
        have hw : |(100571143/250000000 : ℝ)|=(100571143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4702862607/10000000000 : ℝ)|^4185 ≤ (36831946578937/100000000000000 : ℝ)^3161
        have hw : |(4702862607/10000000000 : ℝ)|=(4702862607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533595811/2500000000 : ℝ)*x 0 + (5167077139/10000000000 : ℝ)*x 1 + (5501963063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533595811/2500000000 : ℝ)^4185 ≤ (808856495761/6250000000000 : ℝ)^3161 := by
    have hnat : (533595811 : ℕ)^4185*6250000000000^3161 ≤ 808856495761^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533595811 2500000000 808856495761 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167077139/10000000000 : ℝ)^4185 ≤ (2607541338659/6250000000000 : ℝ)^3161 := by
    have hnat : (5167077139 : ℕ)^4185*6250000000000^3161 ≤ 2607541338659^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167077139 10000000000 2607541338659 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501963063/10000000000 : ℝ)^4185 ≤ (45337634630843/100000000000000 : ℝ)^3161 := by
    have hnat : (5501963063 : ℕ)^4185*100000000000000^3161 ≤ 45337634630843^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501963063 10000000000 45337634630843 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533595811/2500000000 : ℝ), (5167077139/10000000000 : ℝ), (5501963063/10000000000 : ℝ)] ![(808856495761/6250000000000 : ℝ), (2607541338659/6250000000000 : ℝ), (45337634630843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533595811/2500000000 : ℝ)|^4185 ≤ (808856495761/6250000000000 : ℝ)^3161
        have hw : |(-533595811/2500000000 : ℝ)|=(533595811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167077139/10000000000 : ℝ)|^4185 ≤ (2607541338659/6250000000000 : ℝ)^3161
        have hw : |(5167077139/10000000000 : ℝ)|=(5167077139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501963063/10000000000 : ℝ)|^4185 ≤ (45337634630843/100000000000000 : ℝ)^3161
        have hw : |(5501963063/10000000000 : ℝ)|=(5501963063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057207823/2000000000 : ℝ)*x 0 + (-1973379137/10000000000 : ℝ)*x 1 + (2750981533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057207823/2000000000 : ℝ)^4185 ≤ (2149854073291/5000000000000 : ℝ)^3161 := by
    have hnat : (1057207823 : ℕ)^4185*5000000000000^3161 ≤ 2149854073291^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057207823 2000000000 2149854073291 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973379137/10000000000 : ℝ)^4185 ≤ (11665283854187/100000000000000 : ℝ)^3161 := by
    have hnat : (1973379137 : ℕ)^4185*100000000000000^3161 ≤ 11665283854187^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973379137 10000000000 11665283854187 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750981533/5000000000 : ℝ)^4185 ≤ (11334408665893/25000000000000 : ℝ)^3161 := by
    have hnat : (2750981533 : ℕ)^4185*25000000000000^3161 ≤ 11334408665893^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750981533 5000000000 11334408665893 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057207823/2000000000 : ℝ), (-1973379137/10000000000 : ℝ), (2750981533/5000000000 : ℝ)] ![(2149854073291/5000000000000 : ℝ), (11665283854187/100000000000000 : ℝ), (11334408665893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057207823/2000000000 : ℝ)|^4185 ≤ (2149854073291/5000000000000 : ℝ)^3161
        have hw : |(1057207823/2000000000 : ℝ)|=(1057207823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973379137/10000000000 : ℝ)|^4185 ≤ (11665283854187/100000000000000 : ℝ)^3161
        have hw : |(-1973379137/10000000000 : ℝ)|=(1973379137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750981533/5000000000 : ℝ)|^4185 ≤ (11334408665893/25000000000000 : ℝ)^3161
        have hw : |(2750981533/5000000000 : ℝ)|=(2750981533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643019629/5000000000 : ℝ)*x 0 + (2750981533/5000000000 : ℝ)*x 1 + (-1973378939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643019629/5000000000 : ℝ)^4185 ≤ (21498541502901/50000000000000 : ℝ)^3161 := by
    have hnat : (2643019629 : ℕ)^4185*50000000000000^3161 ≤ 21498541502901^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643019629 5000000000 21498541502901 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750981533/5000000000 : ℝ)^4185 ≤ (11334408665893/25000000000000 : ℝ)^3161 := by
    have hnat : (2750981533 : ℕ)^4185*25000000000000^3161 ≤ 11334408665893^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750981533 5000000000 11334408665893 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973378939/10000000000 : ℝ)^4185 ≤ (5832641152291/50000000000000 : ℝ)^3161 := by
    have hnat : (1973378939 : ℕ)^4185*50000000000000^3161 ≤ 5832641152291^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973378939 10000000000 5832641152291 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643019629/5000000000 : ℝ), (2750981533/5000000000 : ℝ), (-1973378939/10000000000 : ℝ)] ![(21498541502901/50000000000000 : ℝ), (11334408665893/25000000000000 : ℝ), (5832641152291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643019629/5000000000 : ℝ)|^4185 ≤ (21498541502901/50000000000000 : ℝ)^3161
        have hw : |(2643019629/5000000000 : ℝ)|=(2643019629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750981533/5000000000 : ℝ)|^4185 ≤ (11334408665893/25000000000000 : ℝ)^3161
        have hw : |(2750981533/5000000000 : ℝ)|=(2750981533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973378939/10000000000 : ℝ)|^4185 ≤ (5832641152291/50000000000000 : ℝ)^3161
        have hw : |(-1973378939/10000000000 : ℝ)|=(1973378939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s2_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173999109/400000000 : ℝ)*x 0 + (4698288131/10000000000 : ℝ)*x 1 + (4027463967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173999109/400000000 : ℝ)^4185 ≤ (16609080584987/50000000000000 : ℝ)^3161 := by
    have hnat : (173999109 : ℕ)^4185*50000000000000^3161 ≤ 16609080584987^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173999109 400000000 16609080584987 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698288131/10000000000 : ℝ)^4185 ≤ (36784521697221/100000000000000 : ℝ)^3161 := by
    have hnat : (4698288131 : ℕ)^4185*100000000000000^3161 ≤ 36784521697221^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698288131 10000000000 36784521697221 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027463967/10000000000 : ℝ)^4185 ≤ (29997317126903/100000000000000 : ℝ)^3161 := by
    have hnat : (4027463967 : ℕ)^4185*100000000000000^3161 ≤ 29997317126903^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027463967 10000000000 29997317126903 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173999109/400000000 : ℝ), (4698288131/10000000000 : ℝ), (4027463967/10000000000 : ℝ)] ![(16609080584987/50000000000000 : ℝ), (36784521697221/100000000000000 : ℝ), (29997317126903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173999109/400000000 : ℝ)|^4185 ≤ (16609080584987/50000000000000 : ℝ)^3161
        have hw : |(173999109/400000000 : ℝ)|=(173999109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698288131/10000000000 : ℝ)|^4185 ≤ (36784521697221/100000000000000 : ℝ)^3161
        have hw : |(4698288131/10000000000 : ℝ)|=(4698288131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027463967/10000000000 : ℝ)|^4185 ≤ (29997317126903/100000000000000 : ℝ)^3161
        have hw : |(4027463967/10000000000 : ℝ)|=(4027463967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (41/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (507/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (507/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (507/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (507/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (507/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (507/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5843/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (182380786324903/20000000000000000000 : ℝ) := by
    have hpowers : (5843/100000 : ℝ)^8369 ≤ (182380786324903/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5843 : ℕ)^8369*20000000000000000000^2048 ≤ 182380786324903^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5843 100000 182380786324903 20000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5843/100000 : ℝ)) (X := (182380786324903/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (507/2500 : ℝ) ^ (8369/2048 : ℝ) ≤ (29472339044542733/20000000000000000000 : ℝ) := by
    have hpowers : (507/2500 : ℝ)^8369 ≤ (29472339044542733/20000000000000000000 : ℝ)^2048 := by
      have hnat : (507 : ℕ)^8369*20000000000000000000^2048 ≤ 29472339044542733^2048*2500^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        507 2500 29472339044542733 20000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (507/2500 : ℝ)) (X := (29472339044542733/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000182380786324903/10000000000000000000 : ℝ) ≤ (5000022315287241/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (10000182380786324903/10000000000000000000 : ℝ)^2048 ≤ (5000022315287241/5000000000000000 : ℝ)^8369 := by
      have hnat : (10000182380786324903 : ℕ)^2048*5000000000000000^8369 ≤ 5000022315287241^8369*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000182380786324903 10000000000000000000 5000022315287241 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000022315287241/5000000000000000 : ℝ)) (X := (10000182380786324903/10000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5007413679957716909/5000000000000000000 : ℝ) ≤ (10003626412269549/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (5007413679957716909/5000000000000000000 : ℝ)^2048 ≤ (10003626412269549/10000000000000000 : ℝ)^8369 := by
      have hnat : (5007413679957716909 : ℕ)^2048*10000000000000000^8369 ≤ 10003626412269549^8369*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5007413679957716909 5000000000000000000 10003626412269549 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003626412269549/10000000000000000 : ℝ)) (X := (5007413679957716909/5000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10029472339044542733/10000000000000000000 : ℝ) ≤ (1250901024245577/1250000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (10029472339044542733/10000000000000000000 : ℝ)^2048 ≤ (1250901024245577/1250000000000000 : ℝ)^8369 := by
      have hnat : (10029472339044542733 : ℕ)^2048*1250000000000000^8369 ≤ 1250901024245577^8369*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029472339044542733 10000000000000000000 1250901024245577 1250000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250901024245577/1250000000000000 : ℝ)) (X := (10029472339044542733/10000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(182380786324903/20000000000000000000 : ℝ) ≤ ((18041098453839405459/18046250000000000000 : ℝ)+2*(3581781695067/1443700000000000 : ℝ)*(5843/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (18041098453839405459/18046250000000000000 : ℝ)+2*(3581781695067/1443700000000000 : ℝ)*(5843/100000 : ℝ)=(5000022315287241/5000000000000000 : ℝ) by norm_num, show 1+2*(182380786324903/20000000000000000000 : ℝ)=(10000182380786324903/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29472339044542733/20000000000000000000 : ℝ)+(182380786324903/20000000000000000000 : ℝ) ≤ ((18041098453839405459/18046250000000000000 : ℝ)+(3581781695067/1443700000000000 : ℝ)*((507/2500 : ℝ)+(5843/100000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (18041098453839405459/18046250000000000000 : ℝ)+(3581781695067/1443700000000000 : ℝ)*((507/2500 : ℝ)+(5843/100000 : ℝ))=(10003626412269549/10000000000000000 : ℝ) by norm_num, show 1+(29472339044542733/20000000000000000000 : ℝ)+(182380786324903/20000000000000000000 : ℝ)=(5007413679957716909/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29472339044542733/20000000000000000000 : ℝ) ≤ ((18041098453839405459/18046250000000000000 : ℝ)+2*(3581781695067/1443700000000000 : ℝ)*(507/2500 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (18041098453839405459/18046250000000000000 : ℝ)+2*(3581781695067/1443700000000000 : ℝ)*(507/2500 : ℝ)=(1250901024245577/1250000000000000 : ℝ) by norm_num, show 1+2*(29472339044542733/20000000000000000000 : ℝ)=(10029472339044542733/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18041098453839405459/18046250000000000000 : ℝ)*(X 1 0+X 2 0)+(3581781695067/1443700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5843/100000 : ℝ)) (hi := (507/2500 : ℝ)) (c := (18041098453839405459/18046250000000000000 : ℝ)) (alpha := (3581781695067/1443700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18041098453839405459/18046250000000000000 : ℝ)*(X 0 1+X 2 1)+(3581781695067/1443700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5843/100000 : ℝ)) (hi := (507/2500 : ℝ)) (c := (18041098453839405459/18046250000000000000 : ℝ)) (alpha := (3581781695067/1443700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18041098453839405459/18046250000000000000 : ℝ)*(X 0 2+X 1 2)+(3581781695067/1443700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5843/100000 : ℝ)) (hi := (507/2500 : ℝ)) (c := (18041098453839405459/18046250000000000000 : ℝ)) (alpha := (3581781695067/1443700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134290693/10000000000 : ℝ)*X 0 0+(2752134883/5000000000 : ℝ)*X 0 1+(322799513/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372372313/10000000000 : ℝ)*X 1 0+(-2310548093/10000000000 : ℝ)*X 1 1+(5164795441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074474649/2000000000 : ℝ)*X 2 0+(129119851/250000000 : ℝ)*X 2 1+(-1155274343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349790513/10000000000 : ℝ)*X 0 0+(100571143/250000000 : ℝ)*X 0 1+(4702862607/10000000000 : ℝ)*X 0 2+(4349790513/10000000000 : ℝ)*X 1 0+(100571143/250000000 : ℝ)*X 1 1+(4702862607/10000000000 : ℝ)*X 1 2+(4349790513/10000000000 : ℝ)*X 2 0+(100571143/250000000 : ℝ)*X 2 1+(4702862607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533595811/2500000000 : ℝ)*X 0 0+(5167077139/10000000000 : ℝ)*X 0 1+(5501963063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057207823/2000000000 : ℝ)*X 1 0+(-1973379137/10000000000 : ℝ)*X 1 1+(2750981533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643019629/5000000000 : ℝ)*X 2 0+(2750981533/5000000000 : ℝ)*X 2 1+(-1973378939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173999109/400000000 : ℝ)*X 0 0+(4698288131/10000000000 : ℝ)*X 0 1+(4027463967/10000000000 : ℝ)*X 0 2+(173999109/400000000 : ℝ)*X 1 0+(4698288131/10000000000 : ℝ)*X 1 1+(4027463967/10000000000 : ℝ)*X 1 2+(173999109/400000000 : ℝ)*X 2 0+(4698288131/10000000000 : ℝ)*X 2 1+(4027463967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155899593387244126442118543/36092500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5757641/5000000000000 : ℝ)*(base19) + (554989029/100000000000000 : ℝ)*(base23) + (124583399/100000000000000 : ℝ)*(upper2) + (41603291/12500000000000 : ℝ)*(upper3) + (32566107/20000000000000 : ℝ)*(upper4) + (88326206945041/4000000000000 : ℝ)*(major0) + (88326206945041/4000000000000 : ℝ)*(major1) + (88326206945041/4000000000000 : ℝ)*(major2) + (1472863243490553/50000000000000 : ℝ)*(sp0) + (294574639764767/10000000000000 : ℝ)*(sp1) + (1472872978905731/50000000000000 : ℝ)*(sp2) + (1470555739403329/100000000000000 : ℝ)*(sp3) + (4005163877/20000000000000 : ℝ)*(sp4) + (3975533351/50000000000000 : ℝ)*(sp7) + (1470563690470031/100000000000000 : ℝ)*(f.failure) + (2945746512800491/100000000000000 : ℝ)*(f.sum) + (36226894875481/7218500000000000000000000000 : ℝ)*base65 + (165562200890588681/72185000000000000000000000000000 : ℝ)*base68 + (675798068302683681/72185000000000000000000000000000 : ℝ)*base70 + (492469409907871319/72185000000000000000000000000000 : ℝ)*base71 + (29701313530749/14437000000000000000000000000 : ℝ)*base74 + (273515949952421319/72185000000000000000000000000000 : ℝ)*base75 + (18490177254071319/72185000000000000000000000000000 : ℝ)*base77 + (409340378174146319/72185000000000000000000000000000 : ℝ)*base79 + (706976759853/288740000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3935601/5000000000000000000000 : ℝ)*base90 + (3935601/5000000000000000000000 : ℝ)*base92 + (3935601/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (539308791835486643801416017/225578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (717132221/100000000000000 : ℝ)*(base19) + (182978137/20000000000000 : ℝ)*(base23) + (342533/1000000000000 : ℝ)*(upper2) + (24735379/25000000000000 : ℝ)*(upper3) + (5469201/10000000000000 : ℝ)*(upper5) + (69949920438471/3125000000000 : ℝ)*(major0) + (69949920438471/3125000000000 : ℝ)*(major1) + (69949920438471/3125000000000 : ℝ)*(major2) + (6659092263/100000000000000 : ℝ)*(sp1) + (4926888551/50000000000000 : ℝ)*(sp2) + (746522676433967/25000000000000 : ℝ)*(sp4) + (2986083329511383/100000000000000 : ℝ)*(sp5) + (37325999213351/1250000000000 : ℝ)*(sp6) + (149070412263343/10000000000000 : ℝ)*(sp7) + (149070412263343/10000000000000 : ℝ)*(f.failure) + (746522676433967/25000000000000 : ℝ)*(f.sum) + (128583539109297/36092500000000000000000000000 : ℝ)*base65 + (102726818360842003/112789062500000000000000000000000 : ℝ)*base67 + (704465544964404503/112789062500000000000000000000000 : ℝ)*base69 + (1098669339082060753/112789062500000000000000000000000 : ℝ)*base71 + (2906502404409/1127890625000000000000000000 : ℝ)*base74 + (1349579324879605881/225578125000000000000000000000000 : ℝ)*base75 + (43329542026919379/3524658203125000000000000000000 : ℝ)*base77 + (252681714513998253/112789062500000000000000000000000 : ℝ)*base79 + (80251684003997/36092500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6937553/500000000000000000000 : ℝ)*base90 + (6937553/500000000000000000000 : ℝ)*base92 + (6937553/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1177_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1177_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1177_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1177_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (41/250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
