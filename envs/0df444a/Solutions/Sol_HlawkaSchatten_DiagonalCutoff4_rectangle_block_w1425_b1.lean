-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:51.019634+00:00
-- url     : https://prove2.me/submissions/88857b5c-eb0a-4c2f-824c-a192181c3a48

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
theorem support_rectangle_w1425_s3_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-123331119/625000000 : ℝ)*x 0 + (338605511/625000000 : ℝ)*x 1 + (2619133279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123331119/625000000 : ℝ)^4385 ≤ (12035333651891/100000000000000 : ℝ)^3361 := by
    have hnat : (123331119 : ℕ)^4385*100000000000000^3361 ≤ 12035333651891^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123331119 625000000 12035333651891 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338605511/625000000 : ℝ)^4385 ≤ (44948457298381/100000000000000 : ℝ)^3361 := by
    have hnat : (338605511 : ℕ)^4385*100000000000000^3361 ≤ 44948457298381^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338605511 625000000 44948457298381 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619133279/5000000000 : ℝ)^4385 ≤ (43016209024251/100000000000000 : ℝ)^3361 := by
    have hnat : (2619133279 : ℕ)^4385*100000000000000^3361 ≤ 43016209024251^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619133279 5000000000 43016209024251 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123331119/625000000 : ℝ), (338605511/625000000 : ℝ), (2619133279/5000000000 : ℝ)] ![(12035333651891/100000000000000 : ℝ), (44948457298381/100000000000000 : ℝ), (43016209024251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123331119/625000000 : ℝ)|^4385 ≤ (12035333651891/100000000000000 : ℝ)^3361
        have hw : |(-123331119/625000000 : ℝ)|=(123331119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338605511/625000000 : ℝ)|^4385 ≤ (44948457298381/100000000000000 : ℝ)^3361
        have hw : |(338605511/625000000 : ℝ)|=(338605511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619133279/5000000000 : ℝ)|^4385 ≤ (43016209024251/100000000000000 : ℝ)^3361
        have hw : |(2619133279/5000000000 : ℝ)|=(2619133279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349801541/10000000000 : ℝ)*x 0 + (-1032413771/5000000000 : ℝ)*x 1 + (2619133267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349801541/10000000000 : ℝ)^4385 ≤ (8843007059749/20000000000000 : ℝ)^3361 := by
    have hnat : (5349801541 : ℕ)^4385*20000000000000^3361 ≤ 8843007059749^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349801541 10000000000 8843007059749 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032413771/5000000000 : ℝ)^4385 ≤ (6384377958369/50000000000000 : ℝ)^3361 := by
    have hnat : (1032413771 : ℕ)^4385*50000000000000^3361 ≤ 6384377958369^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032413771 5000000000 6384377958369 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619133267/5000000000 : ℝ)^4385 ≤ (43016208767119/100000000000000 : ℝ)^3361 := by
    have hnat : (2619133267 : ℕ)^4385*100000000000000^3361 ≤ 43016208767119^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619133267 5000000000 43016208767119 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349801541/10000000000 : ℝ), (-1032413771/5000000000 : ℝ), (2619133267/5000000000 : ℝ)] ![(8843007059749/20000000000000 : ℝ), (6384377958369/50000000000000 : ℝ), (43016208767119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349801541/10000000000 : ℝ)|^4385 ≤ (8843007059749/20000000000000 : ℝ)^3361
        have hw : |(5349801541/10000000000 : ℝ)|=(5349801541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032413771/5000000000 : ℝ)|^4385 ≤ (6384377958369/50000000000000 : ℝ)^3361
        have hw : |(-1032413771/5000000000 : ℝ)|=(1032413771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619133267/5000000000 : ℝ)|^4385 ≤ (43016208767119/100000000000000 : ℝ)^3361
        have hw : |(2619133267/5000000000 : ℝ)|=(2619133267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349801563/10000000000 : ℝ)*x 0 + (130956663/250000000 : ℝ)*x 1 + (-2064827531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349801563/10000000000 : ℝ)^4385 ≤ (1381719860499/3125000000000 : ℝ)^3361 := by
    have hnat : (5349801563 : ℕ)^4385*3125000000000^3361 ≤ 1381719860499^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349801563 10000000000 1381719860499 3125000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130956663/250000000 : ℝ)^4385 ≤ (344129668937/800000000000 : ℝ)^3361 := by
    have hnat : (130956663 : ℕ)^4385*800000000000^3361 ≤ 344129668937^3361*250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130956663 250000000 344129668937 800000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064827531/10000000000 : ℝ)^4385 ≤ (1276875582799/10000000000000 : ℝ)^3361 := by
    have hnat : (2064827531 : ℕ)^4385*10000000000000^3361 ≤ 1276875582799^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064827531 10000000000 1276875582799 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349801563/10000000000 : ℝ), (130956663/250000000 : ℝ), (-2064827531/10000000000 : ℝ)] ![(1381719860499/3125000000000 : ℝ), (344129668937/800000000000 : ℝ), (1276875582799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349801563/10000000000 : ℝ)|^4385 ≤ (1381719860499/3125000000000 : ℝ)^3361
        have hw : |(5349801563/10000000000 : ℝ)|=(5349801563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130956663/250000000 : ℝ)|^4385 ≤ (344129668937/800000000000 : ℝ)^3361
        have hw : |(130956663/250000000 : ℝ)|=(130956663/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064827531/10000000000 : ℝ)|^4385 ≤ (1276875582799/10000000000000 : ℝ)^3361
        have hw : |(-2064827531/10000000000 : ℝ)|=(2064827531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076178401/2500000000 : ℝ)*x 0 + (4114852493/10000000000 : ℝ)*x 1 + (281402031/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076178401/2500000000 : ℝ)^4385 ≤ (33297958793817/100000000000000 : ℝ)^3361 := by
    have hnat : (1076178401 : ℕ)^4385*100000000000000^3361 ≤ 33297958793817^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076178401 2500000000 33297958793817 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114852493/10000000000 : ℝ)^4385 ≤ (15697450340271/50000000000000 : ℝ)^3361 := by
    have hnat : (4114852493 : ℕ)^4385*50000000000000^3361 ≤ 15697450340271^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114852493 10000000000 15697450340271 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281402031/625000000 : ℝ)^4385 ≤ (137918517633/390625000000 : ℝ)^3361 := by
    have hnat : (281402031 : ℕ)^4385*390625000000^3361 ≤ 137918517633^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281402031 625000000 137918517633 390625000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076178401/2500000000 : ℝ), (4114852493/10000000000 : ℝ), (281402031/625000000 : ℝ)] ![(33297958793817/100000000000000 : ℝ), (15697450340271/50000000000000 : ℝ), (137918517633/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076178401/2500000000 : ℝ)|^4385 ≤ (33297958793817/100000000000000 : ℝ)^3361
        have hw : |(1076178401/2500000000 : ℝ)|=(1076178401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114852493/10000000000 : ℝ)|^4385 ≤ (15697450340271/50000000000000 : ℝ)^3361
        have hw : |(4114852493/10000000000 : ℝ)|=(4114852493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281402031/625000000 : ℝ)|^4385 ≤ (137918517633/390625000000 : ℝ)^3361
        have hw : |(281402031/625000000 : ℝ)|=(281402031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61666041/312500000 : ℝ)*x 0 + (5238984241/10000000000 : ℝ)*x 1 + (84640101/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61666041/312500000 : ℝ)^4385 ≤ (12035456258351/100000000000000 : ℝ)^3361 := by
    have hnat : (61666041 : ℕ)^4385*100000000000000^3361 ≤ 12035456258351^3361*312500000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61666041 312500000 12035456258351 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238984241/10000000000 : ℝ)^4385 ≤ (860477966677/2000000000000 : ℝ)^3361 := by
    have hnat : (5238984241 : ℕ)^4385*2000000000000^3361 ≤ 860477966677^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238984241 10000000000 860477966677 2000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84640101/156250000 : ℝ)^4385 ≤ (4494064539283/10000000000000 : ℝ)^3361 := by
    have hnat : (84640101 : ℕ)^4385*10000000000000^3361 ≤ 4494064539283^3361*156250000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84640101 156250000 4494064539283 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61666041/312500000 : ℝ), (5238984241/10000000000 : ℝ), (84640101/156250000 : ℝ)] ![(12035456258351/100000000000000 : ℝ), (860477966677/2000000000000 : ℝ), (4494064539283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61666041/312500000 : ℝ)|^4385 ≤ (12035456258351/100000000000000 : ℝ)^3361
        have hw : |(-61666041/312500000 : ℝ)|=(61666041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238984241/10000000000 : ℝ)|^4385 ≤ (860477966677/2000000000000 : ℝ)^3361
        have hw : |(5238984241/10000000000 : ℝ)|=(5238984241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84640101/156250000 : ℝ)|^4385 ≤ (4494064539283/10000000000000 : ℝ)^3361
        have hw : |(84640101/156250000 : ℝ)|=(84640101/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303175853/10000000000 : ℝ)*x 0 + (-377225503/2000000000 : ℝ)*x 1 + (5416966477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303175853/10000000000 : ℝ)^4385 ≤ (43712946548153/100000000000000 : ℝ)^3361 := by
    have hnat : (5303175853 : ℕ)^4385*100000000000000^3361 ≤ 43712946548153^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303175853 10000000000 43712946548153 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377225503/2000000000 : ℝ)^4385 ≤ (2269281581029/20000000000000 : ℝ)^3361 := by
    have hnat : (377225503 : ℕ)^4385*20000000000000^3361 ≤ 2269281581029^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377225503 2000000000 2269281581029 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416966477/10000000000 : ℝ)^4385 ≤ (44940645533541/100000000000000 : ℝ)^3361 := by
    have hnat : (5416966477 : ℕ)^4385*100000000000000^3361 ≤ 44940645533541^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416966477 10000000000 44940645533541 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303175853/10000000000 : ℝ), (-377225503/2000000000 : ℝ), (5416966477/10000000000 : ℝ)] ![(43712946548153/100000000000000 : ℝ), (2269281581029/20000000000000 : ℝ), (44940645533541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303175853/10000000000 : ℝ)|^4385 ≤ (43712946548153/100000000000000 : ℝ)^3361
        have hw : |(5303175853/10000000000 : ℝ)|=(5303175853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377225503/2000000000 : ℝ)|^4385 ≤ (2269281581029/20000000000000 : ℝ)^3361
        have hw : |(-377225503/2000000000 : ℝ)|=(377225503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416966477/10000000000 : ℝ)|^4385 ≤ (44940645533541/100000000000000 : ℝ)^3361
        have hw : |(5416966477/10000000000 : ℝ)|=(5416966477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303175849/10000000000 : ℝ)*x 0 + (84640101/156250000 : ℝ)*x 1 + (-943063769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303175849/10000000000 : ℝ)^4385 ≤ (2732059156571/6250000000000 : ℝ)^3361 := by
    have hnat : (5303175849 : ℕ)^4385*6250000000000^3361 ≤ 2732059156571^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303175849 10000000000 2732059156571 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84640101/156250000 : ℝ)^4385 ≤ (4494064539283/10000000000000 : ℝ)^3361 := by
    have hnat : (84640101 : ℕ)^4385*10000000000000^3361 ≤ 4494064539283^3361*156250000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84640101 156250000 4494064539283 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943063769/5000000000 : ℝ)^4385 ≤ (11346408085661/100000000000000 : ℝ)^3361 := by
    have hnat : (943063769 : ℕ)^4385*100000000000000^3361 ≤ 11346408085661^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943063769 5000000000 11346408085661 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303175849/10000000000 : ℝ), (84640101/156250000 : ℝ), (-943063769/5000000000 : ℝ)] ![(2732059156571/6250000000000 : ℝ), (4494064539283/10000000000000 : ℝ), (11346408085661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303175849/10000000000 : ℝ)|^4385 ≤ (2732059156571/6250000000000 : ℝ)^3361
        have hw : |(5303175849/10000000000 : ℝ)|=(5303175849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84640101/156250000 : ℝ)|^4385 ≤ (4494064539283/10000000000000 : ℝ)^3361
        have hw : |(84640101/156250000 : ℝ)|=(84640101/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-943063769/5000000000 : ℝ)|^4385 ≤ (11346408085661/100000000000000 : ℝ)^3361
        have hw : |(-943063769/5000000000 : ℝ)|=(943063769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s3_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076186787/2500000000 : ℝ)*x 0 + (4500882391/10000000000 : ℝ)*x 1 + (1029102879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076186787/2500000000 : ℝ)^4385 ≤ (33298297318079/100000000000000 : ℝ)^3361 := by
    have hnat : (1076186787 : ℕ)^4385*100000000000000^3361 ≤ 33298297318079^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076186787 2500000000 33298297318079 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500882391/10000000000 : ℝ)^4385 ≤ (8822820570591/25000000000000 : ℝ)^3361 := by
    have hnat : (4500882391 : ℕ)^4385*25000000000000^3361 ≤ 8822820570591^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500882391 10000000000 8822820570591 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029102879/2500000000 : ℝ)^4385 ≤ (31410420387353/100000000000000 : ℝ)^3361 := by
    have hnat : (1029102879 : ℕ)^4385*100000000000000^3361 ≤ 31410420387353^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029102879 2500000000 31410420387353 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076186787/2500000000 : ℝ), (4500882391/10000000000 : ℝ), (1029102879/2500000000 : ℝ)] ![(33298297318079/100000000000000 : ℝ), (8822820570591/25000000000000 : ℝ), (31410420387353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076186787/2500000000 : ℝ)|^4385 ≤ (33298297318079/100000000000000 : ℝ)^3361
        have hw : |(1076186787/2500000000 : ℝ)|=(1076186787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500882391/10000000000 : ℝ)|^4385 ≤ (8822820570591/25000000000000 : ℝ)^3361
        have hw : |(4500882391/10000000000 : ℝ)|=(4500882391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029102879/2500000000 : ℝ)|^4385 ≤ (31410420387353/100000000000000 : ℝ)^3361
        have hw : |(1029102879/2500000000 : ℝ)|=(1029102879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14949/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3953/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5173/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3953/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5173/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3953/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5173/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3953/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5173/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3953/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5173/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3953/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5173/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5173/50000 : ℝ) ^ (137/32 : ℝ) ≤ (48426673932421/800000000000000000 : ℝ) := by
    have hpowers : (5173/50000 : ℝ)^137 ≤ (48426673932421/800000000000000000 : ℝ)^32 := by
      have hnat : (5173 : ℕ)^137*800000000000000000^32 ≤ 48426673932421^32*50000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5173 50000 48426673932421 800000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5173/50000 : ℝ)) (X := (48426673932421/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (3953/25000 : ℝ) ^ (137/32 : ℝ) ≤ (290704859846243/781250000000000000 : ℝ) := by
    have hpowers : (3953/25000 : ℝ)^137 ≤ (290704859846243/781250000000000000 : ℝ)^32 := by
      have hnat : (3953 : ℕ)^137*781250000000000000^32 ≤ 290704859846243^32*25000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3953 25000 290704859846243 781250000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3953/25000 : ℝ)) (X := (290704859846243/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (400048426673932421/400000000000000000 : ℝ) ≤ (5000141385189423/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (400048426673932421/400000000000000000 : ℝ)^32 ≤ (5000141385189423/5000000000000000 : ℝ)^137 := by
      have hnat : (400048426673932421 : ℕ)^32*5000000000000000^137 ≤ 5000141385189423^137*400000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400048426673932421 400000000000000000 5000141385189423 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141385189423/5000000000000000 : ℝ)) (X := (400048426673932421/400000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043263556301871729/100000000000000000000 : ℝ) ≤ (2500252592031651/2500000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (100043263556301871729/100000000000000000000 : ℝ)^32 ≤ (2500252592031651/2500000000000000 : ℝ)^137 := by
      have hnat : (100043263556301871729 : ℕ)^32*2500000000000000^137 ≤ 2500252592031651^137*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043263556301871729 100000000000000000000 2500252592031651 2500000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500252592031651/2500000000000000 : ℝ)) (X := (100043263556301871729/100000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (390915704859846243/390625000000000000 : ℝ) ≤ (5000868982937181/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (390915704859846243/390625000000000000 : ℝ)^32 ≤ (5000868982937181/5000000000000000 : ℝ)^137 := by
      have hnat : (390915704859846243 : ℕ)^32*5000000000000000^137 ≤ 5000868982937181^137*390625000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390915704859846243 390625000000000000 5000868982937181 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000868982937181/5000000000000000 : ℝ)) (X := (390915704859846243/390625000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48426673932421/800000000000000000 : ℝ) ≤ ((182154967234313879/182200000000000000 : ℝ)+2*(121266291293/91100000000000 : ℝ)*(5173/50000 : ℝ))^(137/32 : ℝ) := by
    rw [show (182154967234313879/182200000000000000 : ℝ)+2*(121266291293/91100000000000 : ℝ)*(5173/50000 : ℝ)=(5000141385189423/5000000000000000 : ℝ) by norm_num, show 1+2*(48426673932421/800000000000000000 : ℝ)=(400048426673932421/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(290704859846243/781250000000000000 : ℝ)+(48426673932421/800000000000000000 : ℝ) ≤ ((182154967234313879/182200000000000000 : ℝ)+(121266291293/91100000000000 : ℝ)*((3953/25000 : ℝ)+(5173/50000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (182154967234313879/182200000000000000 : ℝ)+(121266291293/91100000000000 : ℝ)*((3953/25000 : ℝ)+(5173/50000 : ℝ))=(2500252592031651/2500000000000000 : ℝ) by norm_num, show 1+(290704859846243/781250000000000000 : ℝ)+(48426673932421/800000000000000000 : ℝ)=(100043263556301871729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(290704859846243/781250000000000000 : ℝ) ≤ ((182154967234313879/182200000000000000 : ℝ)+2*(121266291293/91100000000000 : ℝ)*(3953/25000 : ℝ))^(137/32 : ℝ) := by
    rw [show (182154967234313879/182200000000000000 : ℝ)+2*(121266291293/91100000000000 : ℝ)*(3953/25000 : ℝ)=(5000868982937181/5000000000000000 : ℝ) by norm_num, show 1+2*(290704859846243/781250000000000000 : ℝ)=(390915704859846243/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (182154967234313879/182200000000000000 : ℝ)*(X 1 0+X 2 0)+(121266291293/91100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (5173/50000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (182154967234313879/182200000000000000 : ℝ)) (alpha := (121266291293/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (182154967234313879/182200000000000000 : ℝ)*(X 0 1+X 2 1)+(121266291293/91100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (5173/50000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (182154967234313879/182200000000000000 : ℝ)) (alpha := (121266291293/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (182154967234313879/182200000000000000 : ℝ)*(X 0 2+X 1 2)+(121266291293/91100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (5173/50000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (182154967234313879/182200000000000000 : ℝ)) (alpha := (121266291293/91100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-123331119/625000000 : ℝ)*X 0 0+(338605511/625000000 : ℝ)*X 0 1+(2619133279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349801541/10000000000 : ℝ)*X 1 0+(-1032413771/5000000000 : ℝ)*X 1 1+(2619133267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349801563/10000000000 : ℝ)*X 2 0+(130956663/250000000 : ℝ)*X 2 1+(-2064827531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076178401/2500000000 : ℝ)*X 0 0+(4114852493/10000000000 : ℝ)*X 0 1+(281402031/625000000 : ℝ)*X 0 2+(1076178401/2500000000 : ℝ)*X 1 0+(4114852493/10000000000 : ℝ)*X 1 1+(281402031/625000000 : ℝ)*X 1 2+(1076178401/2500000000 : ℝ)*X 2 0+(4114852493/10000000000 : ℝ)*X 2 1+(281402031/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61666041/312500000 : ℝ)*X 0 0+(5238984241/10000000000 : ℝ)*X 0 1+(84640101/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303175853/10000000000 : ℝ)*X 1 0+(-377225503/2000000000 : ℝ)*X 1 1+(5416966477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303175849/10000000000 : ℝ)*X 2 0+(84640101/156250000 : ℝ)*X 2 1+(-943063769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076186787/2500000000 : ℝ)*X 0 0+(4500882391/10000000000 : ℝ)*X 0 1+(1029102879/2500000000 : ℝ)*X 0 2+(1076186787/2500000000 : ℝ)*X 1 0+(4500882391/10000000000 : ℝ)*X 1 1+(1029102879/2500000000 : ℝ)*X 1 2+(1076186787/2500000000 : ℝ)*X 2 0+(4500882391/10000000000 : ℝ)*X 2 1+(1029102879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78578878122989883788577/8896484375000000000000000000 : ℝ) := by norm_num
    linear_combination (204092769/12500000000000 : ℝ)*(base19) + (810747381/50000000000000 : ℝ)*(base23) + (232397853/100000000000000 : ℝ)*(upper3) + (9139439/50000000000000 : ℝ)*(upper4) + (3511323/1562500000000 : ℝ)*(upper5) + (15925121683297/390625000000 : ℝ)*(major0) + (15925121683297/390625000000 : ℝ)*(major1) + (15925121683297/390625000000 : ℝ)*(major2) + (5573493606170453/100000000000000 : ℝ)*(sp0) + (222940869075387/4000000000000 : ℝ)*(sp1) + (174172554316627/3125000000000 : ℝ)*(sp2) + (322515669868379/12500000000000 : ℝ)*(sp3) + (29753456373/100000000000000 : ℝ)*(sp4) + (6644427491/50000000000000 : ℝ)*(sp7) + (1290069323901007/50000000000000 : ℝ)*(f.failure) + (5573523359626827/100000000000000 : ℝ)*(f.sum) + (771112186087/569375000000000000000000000 : ℝ)*base65 + (525460564312879/569375000000000000000000000000 : ℝ)*base67 + (1485646413193627/284687500000000000000000000000 : ℝ)*base69 + (798450551012879/569375000000000000000000000000 : ℝ)*base71 + (2507932907/2224121093750000000000000 : ℝ)*base73 + (317209028742377/284687500000000000000000000000 : ℝ)*base75 + (9250111230209/2224121093750000000000000000 : ℝ)*base77 + (5699403011734877/284687500000000000000000000000 : ℝ)*base79 + (3717557308797/569375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1386123/250000000000000000000 : ℝ)*base90 + (1386123/250000000000000000000 : ℝ)*base92 + (1386123/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44122597892075859971161113/4555000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1685251087/100000000000000 : ℝ)*(base19) + (897691709/50000000000000 : ℝ)*(base23) + (210196617/100000000000000 : ℝ)*(upper3) + (54397739/100000000000000 : ℝ)*(lower4) + (6473901/3125000000000 : ℝ)*(upper5) + (2054878660392583/50000000000000 : ℝ)*(major0) + (2054878660392583/50000000000000 : ℝ)*(major1) + (2054878660392583/50000000000000 : ℝ)*(major2) + (31867033307/100000000000000 : ℝ)*(sp1) + (8302126083/25000000000000 : ℝ)*(sp2) + (702317175873069/12500000000000 : ℝ)*(sp4) + (5618503854700157/100000000000000 : ℝ)*(sp5) + (5618502403096801/100000000000000 : ℝ)*(sp6) + (2600976911698117/100000000000000 : ℝ)*(sp7) + (2600976911698117/100000000000000 : ℝ)*(f.failure) + (702317175873069/12500000000000 : ℝ)*(f.sum) + (2307394460289/2277500000000000000000000000 : ℝ)*base65 + (101045357171492543/9110000000000000000000000000000 : ℝ)*base68 + (125862607099802543/9110000000000000000000000000000 : ℝ)*base70 + (63386006856442543/9110000000000000000000000000000 : ℝ)*base72 + (1318048011797/284687500000000000000000000 : ℝ)*base74 + (141595765667692543/9110000000000000000000000000000 : ℝ)*base76 + (82094256914712543/9110000000000000000000000000000 : ℝ)*base78 + (19918996759412543/9110000000000000000000000000000 : ℝ)*base80 + (3730835440543/1138750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2226087/500000000000000000000 : ℝ)*base89 + (2226087/500000000000000000000 : ℝ)*base91 + (2226087/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1425_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_s4_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987109607/5000000000 : ℝ)*x 0 + (5409843213/10000000000 : ℝ)*x 1 + (1311376211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987109607/5000000000 : ℝ)^4385 ≤ (6021332663693/50000000000000 : ℝ)^3361 := by
    have hnat : (987109607 : ℕ)^4385*50000000000000^3361 ≤ 6021332663693^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987109607 5000000000 6021332663693 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409843213/10000000000 : ℝ)^4385 ≤ (560794492527/1250000000000 : ℝ)^3361 := by
    have hnat : (5409843213 : ℕ)^4385*1250000000000^3361 ≤ 560794492527^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409843213 10000000000 560794492527 1250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311376211/2500000000 : ℝ)^4385 ≤ (43093775264877/100000000000000 : ℝ)^3361 := by
    have hnat : (1311376211 : ℕ)^4385*100000000000000^3361 ≤ 43093775264877^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311376211 2500000000 43093775264877 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987109607/5000000000 : ℝ), (5409843213/10000000000 : ℝ), (1311376211/2500000000 : ℝ)] ![(6021332663693/50000000000000 : ℝ), (560794492527/1250000000000 : ℝ), (43093775264877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987109607/5000000000 : ℝ)|^4385 ≤ (6021332663693/50000000000000 : ℝ)^3361
        have hw : |(-987109607/5000000000 : ℝ)|=(987109607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409843213/10000000000 : ℝ)|^4385 ≤ (560794492527/1250000000000 : ℝ)^3361
        have hw : |(5409843213/10000000000 : ℝ)|=(5409843213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311376211/2500000000 : ℝ)|^4385 ≤ (43093775264877/100000000000000 : ℝ)^3361
        have hw : |(1311376211/2500000000 : ℝ)|=(1311376211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347777551/10000000000 : ℝ)*x 0 + (-2057914517/10000000000 : ℝ)*x 1 + (5245505071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347777551/10000000000 : ℝ)^4385 ≤ (22096606092417/50000000000000 : ℝ)^3361 := by
    have hnat : (5347777551 : ℕ)^4385*50000000000000^3361 ≤ 22096606092417^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347777551 10000000000 22096606092417 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057914517/10000000000 : ℝ)^4385 ≤ (12713010099509/100000000000000 : ℝ)^3361 := by
    have hnat : (2057914517 : ℕ)^4385*100000000000000^3361 ≤ 12713010099509^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057914517 10000000000 12713010099509 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245505071/10000000000 : ℝ)^4385 ≤ (5386722212243/12500000000000 : ℝ)^3361 := by
    have hnat : (5245505071 : ℕ)^4385*12500000000000^3361 ≤ 5386722212243^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245505071 10000000000 5386722212243 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347777551/10000000000 : ℝ), (-2057914517/10000000000 : ℝ), (5245505071/10000000000 : ℝ)] ![(22096606092417/50000000000000 : ℝ), (12713010099509/100000000000000 : ℝ), (5386722212243/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347777551/10000000000 : ℝ)|^4385 ≤ (22096606092417/50000000000000 : ℝ)^3361
        have hw : |(5347777551/10000000000 : ℝ)|=(5347777551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057914517/10000000000 : ℝ)|^4385 ≤ (12713010099509/100000000000000 : ℝ)^3361
        have hw : |(-2057914517/10000000000 : ℝ)|=(2057914517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245505071/10000000000 : ℝ)|^4385 ≤ (5386722212243/12500000000000 : ℝ)^3361
        have hw : |(5245505071/10000000000 : ℝ)|=(5245505071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336944397/2500000000 : ℝ)*x 0 + (5245505121/10000000000 : ℝ)*x 1 + (-2572393/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336944397/2500000000 : ℝ)^4385 ≤ (22096606291877/50000000000000 : ℝ)^3361 := by
    have hnat : (1336944397 : ℕ)^4385*50000000000000^3361 ≤ 22096606291877^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336944397 2500000000 22096606291877 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245505121/10000000000 : ℝ)^4385 ≤ (21546889116931/50000000000000 : ℝ)^3361 := by
    have hnat : (5245505121 : ℕ)^4385*50000000000000^3361 ≤ 21546889116931^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245505121 10000000000 21546889116931 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2572393/12500000 : ℝ)^4385 ≤ (12713009156517/100000000000000 : ℝ)^3361 := by
    have hnat : (2572393 : ℕ)^4385*100000000000000^3361 ≤ 12713009156517^3361*12500000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572393 12500000 12713009156517 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336944397/2500000000 : ℝ), (5245505121/10000000000 : ℝ), (-2572393/12500000 : ℝ)] ![(22096606291877/50000000000000 : ℝ), (21546889116931/50000000000000 : ℝ), (12713009156517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336944397/2500000000 : ℝ)|^4385 ≤ (22096606291877/50000000000000 : ℝ)^3361
        have hw : |(1336944397/2500000000 : ℝ)|=(1336944397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245505121/10000000000 : ℝ)|^4385 ≤ (21546889116931/50000000000000 : ℝ)^3361
        have hw : |(5245505121/10000000000 : ℝ)|=(5245505121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2572393/12500000 : ℝ)|^4385 ≤ (12713009156517/100000000000000 : ℝ)^3361
        have hw : |(-2572393/12500000 : ℝ)|=(2572393/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152638831/5000000000 : ℝ)*x 0 + (4131075701/10000000000 : ℝ)*x 1 + (560759153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152638831/5000000000 : ℝ)^4385 ≤ (8325912835993/25000000000000 : ℝ)^3361 := by
    have hnat : (2152638831 : ℕ)^4385*25000000000000^3361 ≤ 8325912835993^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152638831 5000000000 8325912835993 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131075701/10000000000 : ℝ)^4385 ≤ (31556486477257/100000000000000 : ℝ)^3361 := by
    have hnat : (4131075701 : ℕ)^4385*100000000000000^3361 ≤ 31556486477257^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131075701 10000000000 31556486477257 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560759153/1250000000 : ℝ)^4385 ≤ (7027972432309/20000000000000 : ℝ)^3361 := by
    have hnat : (560759153 : ℕ)^4385*20000000000000^3361 ≤ 7027972432309^3361*1250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560759153 1250000000 7027972432309 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152638831/5000000000 : ℝ), (4131075701/10000000000 : ℝ), (560759153/1250000000 : ℝ)] ![(8325912835993/25000000000000 : ℝ), (31556486477257/100000000000000 : ℝ), (7027972432309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152638831/5000000000 : ℝ)|^4385 ≤ (8325912835993/25000000000000 : ℝ)^3361
        have hw : |(2152638831/5000000000 : ℝ)|=(2152638831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131075701/10000000000 : ℝ)|^4385 ≤ (31556486477257/100000000000000 : ℝ)^3361
        have hw : |(4131075701/10000000000 : ℝ)|=(4131075701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560759153/1250000000 : ℝ)|^4385 ≤ (7027972432309/20000000000000 : ℝ)^3361
        have hw : |(560759153/1250000000 : ℝ)|=(560759153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987115599/5000000000 : ℝ)*x 0 + (2623053707/5000000000 : ℝ)*x 1 + (5409237443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987115599/5000000000 : ℝ)^4385 ≤ (12042760701503/100000000000000 : ℝ)^3361 := by
    have hnat : (987115599 : ℕ)^4385*100000000000000^3361 ≤ 12042760701503^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987115599 5000000000 12042760701503 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623053707/5000000000 : ℝ)^4385 ≤ (21550116970007/50000000000000 : ℝ)^3361 := by
    have hnat : (2623053707 : ℕ)^4385*50000000000000^3361 ≤ 21550116970007^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623053707 5000000000 21550116970007 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409237443/10000000000 : ℝ)^4385 ≤ (22428502670523/50000000000000 : ℝ)^3361 := by
    have hnat : (5409237443 : ℕ)^4385*50000000000000^3361 ≤ 22428502670523^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409237443 10000000000 22428502670523 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987115599/5000000000 : ℝ), (2623053707/5000000000 : ℝ), (5409237443/10000000000 : ℝ)] ![(12042760701503/100000000000000 : ℝ), (21550116970007/50000000000000 : ℝ), (22428502670523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987115599/5000000000 : ℝ)|^4385 ≤ (12042760701503/100000000000000 : ℝ)^3361
        have hw : |(-987115599/5000000000 : ℝ)|=(987115599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623053707/5000000000 : ℝ)|^4385 ≤ (21550116970007/50000000000000 : ℝ)^3361
        have hw : |(2623053707/5000000000 : ℝ)|=(2623053707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409237443/10000000000 : ℝ)|^4385 ≤ (22428502670523/50000000000000 : ℝ)^3361
        have hw : |(5409237443/10000000000 : ℝ)|=(5409237443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652535561/5000000000 : ℝ)*x 0 + (-947090979/5000000000 : ℝ)*x 1 + (5409237487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652535561/5000000000 : ℝ)^4385 ≤ (2733333101261/6250000000000 : ℝ)^3361 := by
    have hnat : (2652535561 : ℕ)^4385*6250000000000^3361 ≤ 2733333101261^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652535561 5000000000 2733333101261 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947090979/5000000000 : ℝ)^4385 ≤ (11409664540711/100000000000000 : ℝ)^3361 := by
    have hnat : (947090979 : ℕ)^4385*100000000000000^3361 ≤ 11409664540711^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947090979 5000000000 11409664540711 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409237487/10000000000 : ℝ)^4385 ≤ (44857005817091/100000000000000 : ℝ)^3361 := by
    have hnat : (5409237487 : ℕ)^4385*100000000000000^3361 ≤ 44857005817091^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409237487 10000000000 44857005817091 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652535561/5000000000 : ℝ), (-947090979/5000000000 : ℝ), (5409237487/10000000000 : ℝ)] ![(2733333101261/6250000000000 : ℝ), (11409664540711/100000000000000 : ℝ), (44857005817091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652535561/5000000000 : ℝ)|^4385 ≤ (2733333101261/6250000000000 : ℝ)^3361
        have hw : |(2652535561/5000000000 : ℝ)|=(2652535561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947090979/5000000000 : ℝ)|^4385 ≤ (11409664540711/100000000000000 : ℝ)^3361
        have hw : |(-947090979/5000000000 : ℝ)|=(947090979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409237487/10000000000 : ℝ)|^4385 ≤ (44857005817091/100000000000000 : ℝ)^3361
        have hw : |(5409237487/10000000000 : ℝ)|=(5409237487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652535567/5000000000 : ℝ)*x 0 + (2704618747/5000000000 : ℝ)*x 1 + (-947090967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652535567/5000000000 : ℝ)^4385 ≤ (1093333243731/2500000000000 : ℝ)^3361 := by
    have hnat : (2652535567 : ℕ)^4385*2500000000000^3361 ≤ 1093333243731^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652535567 5000000000 1093333243731 2500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704618747/5000000000 : ℝ)^4385 ≤ (1794280235713/4000000000000 : ℝ)^3361 := by
    have hnat : (2704618747 : ℕ)^4385*4000000000000^3361 ≤ 1794280235713^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704618747 5000000000 1794280235713 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947090967/5000000000 : ℝ)^4385 ≤ (5704832176051/50000000000000 : ℝ)^3361 := by
    have hnat : (947090967 : ℕ)^4385*50000000000000^3361 ≤ 5704832176051^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947090967 5000000000 5704832176051 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652535567/5000000000 : ℝ), (2704618747/5000000000 : ℝ), (-947090967/5000000000 : ℝ)] ![(1093333243731/2500000000000 : ℝ), (1794280235713/4000000000000 : ℝ), (5704832176051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652535567/5000000000 : ℝ)|^4385 ≤ (1093333243731/2500000000000 : ℝ)^3361
        have hw : |(2652535567/5000000000 : ℝ)|=(2652535567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704618747/5000000000 : ℝ)|^4385 ≤ (1794280235713/4000000000000 : ℝ)^3361
        have hw : |(2704618747/5000000000 : ℝ)|=(2704618747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947090967/5000000000 : ℝ)|^4385 ≤ (5704832176051/50000000000000 : ℝ)^3361
        have hw : |(-947090967/5000000000 : ℝ)|=(947090967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s4_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076325873/2500000000 : ℝ)*x 0 + (1121192949/2500000000 : ℝ)*x 1 + (4132383953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076325873/2500000000 : ℝ)^4385 ≤ (8325978007323/25000000000000 : ℝ)^3361 := by
    have hnat : (1076325873 : ℕ)^4385*25000000000000^3361 ≤ 8325978007323^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076325873 2500000000 8325978007323 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121192949/2500000000 : ℝ)^4385 ≤ (8781640662181/25000000000000 : ℝ)^3361 := by
    have hnat : (1121192949 : ℕ)^4385*25000000000000^3361 ≤ 8781640662181^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121192949 2500000000 8781640662181 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132383953/10000000000 : ℝ)^4385 ≤ (31569525316507/100000000000000 : ℝ)^3361 := by
    have hnat : (4132383953 : ℕ)^4385*100000000000000^3361 ≤ 31569525316507^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132383953 10000000000 31569525316507 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076325873/2500000000 : ℝ), (1121192949/2500000000 : ℝ), (4132383953/10000000000 : ℝ)] ![(8325978007323/25000000000000 : ℝ), (8781640662181/25000000000000 : ℝ), (31569525316507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076325873/2500000000 : ℝ)|^4385 ≤ (8325978007323/25000000000000 : ℝ)^3361
        have hw : |(1076325873/2500000000 : ℝ)|=(1076325873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121192949/2500000000 : ℝ)|^4385 ≤ (8781640662181/25000000000000 : ℝ)^3361
        have hw : |(1121192949/2500000000 : ℝ)|=(1121192949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132383953/10000000000 : ℝ)|^4385 ≤ (31569525316507/100000000000000 : ℝ)^3361
        have hw : |(4132383953/10000000000 : ℝ)|=(4132383953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1413/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2957/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14949/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14949/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14949/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14949/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14949/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14949/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11149/100000 : ℝ) ^ (137/32 : ℝ) ≤ (4168202093626551/50000000000000000000 : ℝ) := by
    have hpowers : (11149/100000 : ℝ)^137 ≤ (4168202093626551/50000000000000000000 : ℝ)^32 := by
      have hnat : (11149 : ℕ)^137*50000000000000000000^32 ≤ 4168202093626551^32*100000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11149 100000 4168202093626551 50000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11149/100000 : ℝ)) (X := (4168202093626551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (14949/100000 : ℝ) ^ (137/32 : ℝ) ≤ (14631142387581503/50000000000000000000 : ℝ) := by
    have hpowers : (14949/100000 : ℝ)^137 ≤ (14631142387581503/50000000000000000000 : ℝ)^32 := by
      have hnat : (14949 : ℕ)^137*50000000000000000000^32 ≤ 14631142387581503^32*100000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14949 100000 14631142387581503 50000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14949/100000 : ℝ)) (X := (14631142387581503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004168202093626551/25000000000000000000 : ℝ) ≤ (1250048676622533/1250000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (25004168202093626551/25000000000000000000 : ℝ)^32 ≤ (1250048676622533/1250000000000000 : ℝ)^137 := by
      have hnat : (25004168202093626551 : ℕ)^32*1250000000000000^137 ≤ 1250048676622533^137*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004168202093626551 25000000000000000000 1250048676622533 1250000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250048676622533/1250000000000000 : ℝ)) (X := (25004168202093626551/25000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009399672240604027/25000000000000000000 : ℝ) ≤ (5000439045522287/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (25009399672240604027/25000000000000000000 : ℝ)^32 ≤ (5000439045522287/5000000000000000 : ℝ)^137 := by
      have hnat : (25009399672240604027 : ℕ)^32*5000000000000000^137 ≤ 5000439045522287^137*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009399672240604027 25000000000000000000 5000439045522287 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000439045522287/5000000000000000 : ℝ)) (X := (25009399672240604027/25000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014631142387581503/25000000000000000000 : ℝ) ≤ (2500341692277221/2500000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (25014631142387581503/25000000000000000000 : ℝ)^32 ≤ (2500341692277221/2500000000000000 : ℝ)^137 := by
      have hnat : (25014631142387581503 : ℕ)^32*2500000000000000^137 ≤ 2500341692277221^137*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014631142387581503 25000000000000000000 2500341692277221 2500000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500341692277221/2500000000000000 : ℝ)) (X := (25014631142387581503/25000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4168202093626551/50000000000000000000 : ℝ) ≤ ((1899529161292350941/1900000000000000000 : ℝ)+2*(48867806431/38000000000000 : ℝ)*(11149/100000 : ℝ))^(137/32 : ℝ) := by
    rw [show (1899529161292350941/1900000000000000000 : ℝ)+2*(48867806431/38000000000000 : ℝ)*(11149/100000 : ℝ)=(1250048676622533/1250000000000000 : ℝ) by norm_num, show 1+2*(4168202093626551/50000000000000000000 : ℝ)=(25004168202093626551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14631142387581503/50000000000000000000 : ℝ)+(4168202093626551/50000000000000000000 : ℝ) ≤ ((1899529161292350941/1900000000000000000 : ℝ)+(48867806431/38000000000000 : ℝ)*((14949/100000 : ℝ)+(11149/100000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (1899529161292350941/1900000000000000000 : ℝ)+(48867806431/38000000000000 : ℝ)*((14949/100000 : ℝ)+(11149/100000 : ℝ))=(5000439045522287/5000000000000000 : ℝ) by norm_num, show 1+(14631142387581503/50000000000000000000 : ℝ)+(4168202093626551/50000000000000000000 : ℝ)=(25009399672240604027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14631142387581503/50000000000000000000 : ℝ) ≤ ((1899529161292350941/1900000000000000000 : ℝ)+2*(48867806431/38000000000000 : ℝ)*(14949/100000 : ℝ))^(137/32 : ℝ) := by
    rw [show (1899529161292350941/1900000000000000000 : ℝ)+2*(48867806431/38000000000000 : ℝ)*(14949/100000 : ℝ)=(2500341692277221/2500000000000000 : ℝ) by norm_num, show 1+2*(14631142387581503/50000000000000000000 : ℝ)=(25014631142387581503/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1899529161292350941/1900000000000000000 : ℝ)*(X 1 0+X 2 0)+(48867806431/38000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (1899529161292350941/1900000000000000000 : ℝ)) (alpha := (48867806431/38000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1899529161292350941/1900000000000000000 : ℝ)*(X 0 1+X 2 1)+(48867806431/38000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (1899529161292350941/1900000000000000000 : ℝ)) (alpha := (48867806431/38000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1899529161292350941/1900000000000000000 : ℝ)*(X 0 2+X 1 2)+(48867806431/38000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (1899529161292350941/1900000000000000000 : ℝ)) (alpha := (48867806431/38000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987109607/5000000000 : ℝ)*X 0 0+(5409843213/10000000000 : ℝ)*X 0 1+(1311376211/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347777551/10000000000 : ℝ)*X 1 0+(-2057914517/10000000000 : ℝ)*X 1 1+(5245505071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336944397/2500000000 : ℝ)*X 2 0+(5245505121/10000000000 : ℝ)*X 2 1+(-2572393/12500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152638831/5000000000 : ℝ)*X 0 0+(4131075701/10000000000 : ℝ)*X 0 1+(560759153/1250000000 : ℝ)*X 0 2+(2152638831/5000000000 : ℝ)*X 1 0+(4131075701/10000000000 : ℝ)*X 1 1+(560759153/1250000000 : ℝ)*X 1 2+(2152638831/5000000000 : ℝ)*X 2 0+(4131075701/10000000000 : ℝ)*X 2 1+(560759153/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-987115599/5000000000 : ℝ)*X 0 0+(2623053707/5000000000 : ℝ)*X 0 1+(5409237443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652535561/5000000000 : ℝ)*X 1 0+(-947090979/5000000000 : ℝ)*X 1 1+(5409237487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652535567/5000000000 : ℝ)*X 2 0+(2704618747/5000000000 : ℝ)*X 2 1+(-947090967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076325873/2500000000 : ℝ)*X 0 0+(1121192949/2500000000 : ℝ)*X 0 1+(4132383953/10000000000 : ℝ)*X 0 2+(1076325873/2500000000 : ℝ)*X 1 0+(1121192949/2500000000 : ℝ)*X 1 1+(4132383953/10000000000 : ℝ)*X 1 2+(1076325873/2500000000 : ℝ)*X 2 0+(1121192949/2500000000 : ℝ)*X 2 1+(4132383953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130094935062057555311095611/23750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (594387253/100000000000000 : ℝ)*(base19) + (545438467/100000000000000 : ℝ)*(base23) + (760803/1562500000000 : ℝ)*(lower2) + (49198393/100000000000000 : ℝ)*(upper3) + (135855759/100000000000000 : ℝ)*(upper5) + (1112747961228957/25000000000000 : ℝ)*(major0) + (1112747961228957/25000000000000 : ℝ)*(major1) + (1112747961228957/25000000000000 : ℝ)*(major2) + (3042511960829807/50000000000000 : ℝ)*(sp0) + (608504601873911/10000000000000 : ℝ)*(sp1) + (760630758460987/12500000000000 : ℝ)*(sp2) + (176058081909443/6250000000000 : ℝ)*(sp3) + (90765867/400000000000 : ℝ)*(sp4) + (3791782409/50000000000000 : ℝ)*(sp7) + (1408468447057953/50000000000000 : ℝ)*(f.failure) + (6085046613126363/100000000000000 : ℝ)*(f.sum) + (3778313884867/475000000000000000000000000 : ℝ)*base65 + (47317734436251463/47500000000000000000000000000000 : ℝ)*base68 + (66657532051251463/47500000000000000000000000000000 : ℝ)*base70 + (157179729923748537/47500000000000000000000000000000 : ℝ)*base71 + (409673198117/475000000000000000000000000 : ℝ)*base73 + (70711008391251463/47500000000000000000000000000000 : ℝ)*base76 + (5458143881251463/47500000000000000000000000000000 : ℝ)*base78 + (290211036698748537/47500000000000000000000000000000 : ℝ)*base79 + (1283765861117/475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (481317/250000000000000000000 : ℝ)*base90 + (481317/250000000000000000000 : ℝ)*base92 + (481317/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1023360264619606804379526819/95000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10926161/625000000000 : ℝ)*(base19) + (385727481/20000000000000 : ℝ)*(base23) + (7366793/3125000000000 : ℝ)*(upper3) + (67343183/100000000000000 : ℝ)*(lower4) + (98616653/50000000000000 : ℝ)*(upper5) + (4483929676557849/100000000000000 : ℝ)*(major0) + (4483929676557849/100000000000000 : ℝ)*(major1) + (4483929676557849/100000000000000 : ℝ)*(major2) + (18132802941/50000000000000 : ℝ)*(sp1) + (20595137789/50000000000000 : ℝ)*(sp2) + (3065038227769949/50000000000000 : ℝ)*(sp4) + (1226007688349651/20000000000000 : ℝ)*(sp5) + (1226006667325383/20000000000000 : ℝ)*(sp6) + (567556507700403/20000000000000 : ℝ)*(sp7) + (567556507700403/20000000000000 : ℝ)*(f.failure) + (3065038227769949/50000000000000 : ℝ)*(f.sum) + (1416771567481/1900000000000000000000000000 : ℝ)*base66 + (818038672862035909/190000000000000000000000000000000 : ℝ)*base67 + (775460927432035909/190000000000000000000000000000000 : ℝ)*base69 + (1246163628462035909/190000000000000000000000000000000 : ℝ)*base71 + (4415092080519/1900000000000000000000000000 : ℝ)*base73 + (4074001148762035909/190000000000000000000000000000000 : ℝ)*base75 + (239435255882035909/190000000000000000000000000000000 : ℝ)*base77 + (506974059422035909/190000000000000000000000000000000 : ℝ)*base79 + (8171822394581/1900000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (434367/100000000000000000000 : ℝ)*base90 + (434367/100000000000000000000 : ℝ)*base92 + (434367/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_s5_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987178539/5000000000 : ℝ)*x 0 + (5408614813/10000000000 : ℝ)*x 1 + (5246642397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987178539/5000000000 : ℝ)^4385 ≤ (6021881261197/50000000000000 : ℝ)^3361 := by
    have hnat : (987178539 : ℕ)^4385*50000000000000^3361 ≤ 6021881261197^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987178539 5000000000 6021881261197 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408614813/10000000000 : ℝ)^4385 ≤ (22425134549039/50000000000000 : ℝ)^3361 := by
    have hnat : (5408614813 : ℕ)^4385*50000000000000^3361 ≤ 22425134549039^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408614813 10000000000 22425134549039 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246642397/10000000000 : ℝ)^4385 ≤ (21552984185051/50000000000000 : ℝ)^3361 := by
    have hnat : (5246642397 : ℕ)^4385*50000000000000^3361 ≤ 21552984185051^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246642397 10000000000 21552984185051 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987178539/5000000000 : ℝ), (5408614813/10000000000 : ℝ), (5246642397/10000000000 : ℝ)] ![(6021881261197/50000000000000 : ℝ), (22425134549039/50000000000000 : ℝ), (21552984185051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987178539/5000000000 : ℝ)|^4385 ≤ (6021881261197/50000000000000 : ℝ)^3361
        have hw : |(-987178539/5000000000 : ℝ)|=(987178539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408614813/10000000000 : ℝ)|^4385 ≤ (22425134549039/50000000000000 : ℝ)^3361
        have hw : |(5408614813/10000000000 : ℝ)|=(5408614813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246642397/10000000000 : ℝ)|^4385 ≤ (21552984185051/50000000000000 : ℝ)^3361
        have hw : |(5246642397/10000000000 : ℝ)|=(5246642397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347460559/10000000000 : ℝ)*x 0 + (-2056825817/10000000000 : ℝ)*x 1 + (1311660621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347460559/10000000000 : ℝ)^4385 ≤ (22094897266959/50000000000000 : ℝ)^3361 := by
    have hnat : (5347460559 : ℕ)^4385*50000000000000^3361 ≤ 22094897266959^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347460559 10000000000 22094897266959 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056825817/10000000000 : ℝ)^4385 ≤ (6352118072647/50000000000000 : ℝ)^3361 := by
    have hnat : (2056825817 : ℕ)^4385*50000000000000^3361 ≤ 6352118072647^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056825817 10000000000 6352118072647 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311660621/2500000000 : ℝ)^4385 ≤ (43105969302661/100000000000000 : ℝ)^3361 := by
    have hnat : (1311660621 : ℕ)^4385*100000000000000^3361 ≤ 43105969302661^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311660621 2500000000 43105969302661 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347460559/10000000000 : ℝ), (-2056825817/10000000000 : ℝ), (1311660621/2500000000 : ℝ)] ![(22094897266959/50000000000000 : ℝ), (6352118072647/50000000000000 : ℝ), (43105969302661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347460559/10000000000 : ℝ)|^4385 ≤ (22094897266959/50000000000000 : ℝ)^3361
        have hw : |(5347460559/10000000000 : ℝ)|=(5347460559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056825817/10000000000 : ℝ)|^4385 ≤ (6352118072647/50000000000000 : ℝ)^3361
        have hw : |(-2056825817/10000000000 : ℝ)|=(2056825817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311660621/2500000000 : ℝ)|^4385 ≤ (43105969302661/100000000000000 : ℝ)^3361
        have hw : |(1311660621/2500000000 : ℝ)|=(1311660621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347460723/10000000000 : ℝ)*x 0 + (2623321191/5000000000 : ℝ)*x 1 + (-411365147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347460723/10000000000 : ℝ)^4385 ≤ (44189796302069/100000000000000 : ℝ)^3361 := by
    have hnat : (5347460723 : ℕ)^4385*100000000000000^3361 ≤ 44189796302069^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347460723 10000000000 44189796302069 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623321191/5000000000 : ℝ)^4385 ≤ (10776492052329/25000000000000 : ℝ)^3361 := by
    have hnat : (2623321191 : ℕ)^4385*25000000000000^3361 ≤ 10776492052329^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623321191 5000000000 10776492052329 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411365147/2000000000 : ℝ)^4385 ≤ (25408470969/200000000000 : ℝ)^3361 := by
    have hnat : (411365147 : ℕ)^4385*200000000000^3361 ≤ 25408470969^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411365147 2000000000 25408470969 200000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347460723/10000000000 : ℝ), (2623321191/5000000000 : ℝ), (-411365147/2000000000 : ℝ)] ![(44189796302069/100000000000000 : ℝ), (10776492052329/25000000000000 : ℝ), (25408470969/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347460723/10000000000 : ℝ)|^4385 ≤ (44189796302069/100000000000000 : ℝ)^3361
        have hw : |(5347460723/10000000000 : ℝ)|=(5347460723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623321191/5000000000 : ℝ)|^4385 ≤ (10776492052329/25000000000000 : ℝ)^3361
        have hw : |(2623321191/5000000000 : ℝ)|=(2623321191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411365147/2000000000 : ℝ)|^4385 ≤ (25408470969/200000000000 : ℝ)^3361
        have hw : |(-411365147/2000000000 : ℝ)|=(411365147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152680947/5000000000 : ℝ)*x 0 + (4133620781/10000000000 : ℝ)*x 1 + (2241753817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152680947/5000000000 : ℝ)^4385 ≤ (33304501444289/100000000000000 : ℝ)^3361 := by
    have hnat : (2152680947 : ℕ)^4385*100000000000000^3361 ≤ 33304501444289^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152680947 5000000000 33304501444289 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133620781/10000000000 : ℝ)^4385 ≤ (1973865841069/6250000000000 : ℝ)^3361 := by
    have hnat : (4133620781 : ℕ)^4385*6250000000000^3361 ≤ 1973865841069^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133620781 10000000000 1973865841069 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241753817/5000000000 : ℝ)^4385 ≤ (35113645089221/100000000000000 : ℝ)^3361 := by
    have hnat : (2241753817 : ℕ)^4385*100000000000000^3361 ≤ 35113645089221^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241753817 5000000000 35113645089221 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152680947/5000000000 : ℝ), (4133620781/10000000000 : ℝ), (2241753817/5000000000 : ℝ)] ![(33304501444289/100000000000000 : ℝ), (1973865841069/6250000000000 : ℝ), (35113645089221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152680947/5000000000 : ℝ)|^4385 ≤ (33304501444289/100000000000000 : ℝ)^3361
        have hw : |(2152680947/5000000000 : ℝ)|=(2152680947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133620781/10000000000 : ℝ)|^4385 ≤ (1973865841069/6250000000000 : ℝ)^3361
        have hw : |(4133620781/10000000000 : ℝ)|=(4133620781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241753817/5000000000 : ℝ)|^4385 ≤ (35113645089221/100000000000000 : ℝ)^3361
        have hw : |(2241753817/5000000000 : ℝ)|=(2241753817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-493592113/2500000000 : ℝ)*x 0 + (5247227757/10000000000 : ℝ)*x 1 + (169000827/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493592113/2500000000 : ℝ)^4385 ≤ (481754121751/4000000000000 : ℝ)^3361 := by
    have hnat : (493592113 : ℕ)^4385*4000000000000^3361 ≤ 481754121751^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493592113 2500000000 481754121751 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247227757/10000000000 : ℝ)^4385 ≤ (10778060747599/25000000000000 : ℝ)^3361 := by
    have hnat : (5247227757 : ℕ)^4385*25000000000000^3361 ≤ 10778060747599^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247227757 10000000000 10778060747599 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169000827/312500000 : ℝ)^4385 ≤ (44843903958849/100000000000000 : ℝ)^3361 := by
    have hnat : (169000827 : ℕ)^4385*100000000000000^3361 ≤ 44843903958849^3361*312500000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169000827 312500000 44843903958849 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493592113/2500000000 : ℝ), (5247227757/10000000000 : ℝ), (169000827/312500000 : ℝ)] ![(481754121751/4000000000000 : ℝ), (10778060747599/25000000000000 : ℝ), (44843903958849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493592113/2500000000 : ℝ)|^4385 ≤ (481754121751/4000000000000 : ℝ)^3361
        have hw : |(-493592113/2500000000 : ℝ)|=(493592113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247227757/10000000000 : ℝ)|^4385 ≤ (10778060747599/25000000000000 : ℝ)^3361
        have hw : |(5247227757/10000000000 : ℝ)|=(5247227757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169000827/312500000 : ℝ)|^4385 ≤ (44843903958849/100000000000000 : ℝ)^3361
        have hw : |(169000827/312500000 : ℝ)|=(169000827/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530536869/1000000000 : ℝ)*x 0 + (-1895441791/10000000000 : ℝ)*x 1 + (2704013219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530536869/1000000000 : ℝ)^4385 ≤ (43736530079817/100000000000000 : ℝ)^3361 := by
    have hnat : (530536869 : ℕ)^4385*100000000000000^3361 ≤ 43736530079817^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530536869 1000000000 43736530079817 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895441791/10000000000 : ℝ)^4385 ≤ (5709783114369/50000000000000 : ℝ)^3361 := by
    have hnat : (1895441791 : ℕ)^4385*50000000000000^3361 ≤ 5709783114369^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895441791 10000000000 5709783114369 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704013219/5000000000 : ℝ)^4385 ≤ (44843903677569/100000000000000 : ℝ)^3361 := by
    have hnat : (2704013219 : ℕ)^4385*100000000000000^3361 ≤ 44843903677569^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704013219 5000000000 44843903677569 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530536869/1000000000 : ℝ), (-1895441791/10000000000 : ℝ), (2704013219/5000000000 : ℝ)] ![(43736530079817/100000000000000 : ℝ), (5709783114369/50000000000000 : ℝ), (44843903677569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530536869/1000000000 : ℝ)|^4385 ≤ (43736530079817/100000000000000 : ℝ)^3361
        have hw : |(530536869/1000000000 : ℝ)|=(530536869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895441791/10000000000 : ℝ)|^4385 ≤ (5709783114369/50000000000000 : ℝ)^3361
        have hw : |(-1895441791/10000000000 : ℝ)|=(1895441791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704013219/5000000000 : ℝ)|^4385 ≤ (44843903677569/100000000000000 : ℝ)^3361
        have hw : |(2704013219/5000000000 : ℝ)|=(2704013219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305369071/10000000000 : ℝ)*x 0 + (1081605253/2000000000 : ℝ)*x 1 + (-1895441507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305369071/10000000000 : ℝ)^4385 ≤ (8747306835531/20000000000000 : ℝ)^3361 := by
    have hnat : (5305369071 : ℕ)^4385*20000000000000^3361 ≤ 8747306835531^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305369071 10000000000 8747306835531 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081605253/2000000000 : ℝ)^4385 ≤ (22421950902987/50000000000000 : ℝ)^3361 := by
    have hnat : (1081605253 : ℕ)^4385*50000000000000^3361 ≤ 22421950902987^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081605253 2000000000 22421950902987 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895441507/10000000000 : ℝ)^4385 ≤ (11419563996407/100000000000000 : ℝ)^3361 := by
    have hnat : (1895441507 : ℕ)^4385*100000000000000^3361 ≤ 11419563996407^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895441507 10000000000 11419563996407 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305369071/10000000000 : ℝ), (1081605253/2000000000 : ℝ), (-1895441507/10000000000 : ℝ)] ![(8747306835531/20000000000000 : ℝ), (22421950902987/50000000000000 : ℝ), (11419563996407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305369071/10000000000 : ℝ)|^4385 ≤ (8747306835531/20000000000000 : ℝ)^3361
        have hw : |(5305369071/10000000000 : ℝ)|=(5305369071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081605253/2000000000 : ℝ)|^4385 ≤ (22421950902987/50000000000000 : ℝ)^3361
        have hw : |(1081605253/2000000000 : ℝ)|=(1081605253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895441507/10000000000 : ℝ)|^4385 ≤ (11419563996407/100000000000000 : ℝ)^3361
        have hw : |(-1895441507/10000000000 : ℝ)|=(1895441507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s5_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305386507/10000000000 : ℝ)*x 0 + (56028041/125000000 : ℝ)*x 1 + (4134891789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305386507/10000000000 : ℝ)^4385 ≤ (8326187462173/25000000000000 : ℝ)^3361 := by
    have hnat : (4305386507 : ℕ)^4385*25000000000000^3361 ≤ 8326187462173^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305386507 10000000000 8326187462173 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56028041/125000000 : ℝ)^4385 ≤ (8775181669423/25000000000000 : ℝ)^3361 := by
    have hnat : (56028041 : ℕ)^4385*25000000000000^3361 ≤ 8775181669423^3361*125000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56028041 125000000 8775181669423 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4134891789/10000000000 : ℝ)^4385 ≤ (15797261729677/50000000000000 : ℝ)^3361 := by
    have hnat : (4134891789 : ℕ)^4385*50000000000000^3361 ≤ 15797261729677^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134891789 10000000000 15797261729677 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305386507/10000000000 : ℝ), (56028041/125000000 : ℝ), (4134891789/10000000000 : ℝ)] ![(8326187462173/25000000000000 : ℝ), (8775181669423/25000000000000 : ℝ), (15797261729677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305386507/10000000000 : ℝ)|^4385 ≤ (8326187462173/25000000000000 : ℝ)^3361
        have hw : |(4305386507/10000000000 : ℝ)|=(4305386507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56028041/125000000 : ℝ)|^4385 ≤ (8775181669423/25000000000000 : ℝ)^3361
        have hw : |(56028041/125000000 : ℝ)|=(56028041/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4134891789/10000000000 : ℝ)|^4385 ≤ (15797261729677/50000000000000 : ℝ)^3361
        have hw : |(4134891789/10000000000 : ℝ)|=(4134891789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1413/12500 : ℝ) ^ (137/32 : ℝ) ≤ (552751786079733/6250000000000000000 : ℝ) := by
    have hpowers : (1413/12500 : ℝ)^137 ≤ (552751786079733/6250000000000000000 : ℝ)^32 := by
      have hnat : (1413 : ℕ)^137*6250000000000000000^32 ≤ 552751786079733^32*12500^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1413 12500 552751786079733 6250000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1413/12500 : ℝ)) (X := (552751786079733/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2957/20000 : ℝ) ^ (137/32 : ℝ) ≤ (27912424681767267/100000000000000000000 : ℝ) := by
    have hpowers : (2957/20000 : ℝ)^137 ≤ (27912424681767267/100000000000000000000 : ℝ)^32 := by
      have hnat : (2957 : ℕ)^137*100000000000000000000^32 ≤ 27912424681767267^32*20000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 20000 27912424681767267 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/20000 : ℝ)) (X := (27912424681767267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125552751786079733/3125000000000000000 : ℝ) ≤ (10000413123698339/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (3125552751786079733/3125000000000000000 : ℝ)^32 ≤ (10000413123698339/10000000000000000 : ℝ)^137 := by
      have hnat : (3125552751786079733 : ℕ)^32*10000000000000000^137 ≤ 10000413123698339^137*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125552751786079733 3125000000000000000 10000413123698339 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000413123698339/10000000000000000 : ℝ)) (X := (3125552751786079733/3125000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007351290651808599/20000000000000000000 : ℝ) ≤ (10000858423989449/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (20007351290651808599/20000000000000000000 : ℝ)^32 ≤ (10000858423989449/10000000000000000 : ℝ)^137 := by
      have hnat : (20007351290651808599 : ℕ)^32*10000000000000000^137 ≤ 10000858423989449^137*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007351290651808599 20000000000000000000 10000858423989449 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000858423989449/10000000000000000 : ℝ)) (X := (20007351290651808599/20000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027912424681767267/50000000000000000000 : ℝ) ≤ (10001303724280559/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50027912424681767267/50000000000000000000 : ℝ)^32 ≤ (10001303724280559/10000000000000000 : ℝ)^137 := by
      have hnat : (50027912424681767267 : ℕ)^32*10000000000000000^137 ≤ 10001303724280559^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027912424681767267 50000000000000000000 10001303724280559 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001303724280559/10000000000000000 : ℝ)) (X := (50027912424681767267/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(552751786079733/6250000000000000000 : ℝ) ≤ ((34801370734612503179/34810000000000000000 : ℝ)+2*(44530029111/34810000000000 : ℝ)*(1413/12500 : ℝ))^(137/32 : ℝ) := by
    rw [show (34801370734612503179/34810000000000000000 : ℝ)+2*(44530029111/34810000000000 : ℝ)*(1413/12500 : ℝ)=(10000413123698339/10000000000000000 : ℝ) by norm_num, show 1+2*(552751786079733/6250000000000000000 : ℝ)=(3125552751786079733/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27912424681767267/100000000000000000000 : ℝ)+(552751786079733/6250000000000000000 : ℝ) ≤ ((34801370734612503179/34810000000000000000 : ℝ)+(44530029111/34810000000000 : ℝ)*((2957/20000 : ℝ)+(1413/12500 : ℝ)))^(137/32 : ℝ) := by
    rw [show (34801370734612503179/34810000000000000000 : ℝ)+(44530029111/34810000000000 : ℝ)*((2957/20000 : ℝ)+(1413/12500 : ℝ))=(10000858423989449/10000000000000000 : ℝ) by norm_num, show 1+(27912424681767267/100000000000000000000 : ℝ)+(552751786079733/6250000000000000000 : ℝ)=(20007351290651808599/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27912424681767267/100000000000000000000 : ℝ) ≤ ((34801370734612503179/34810000000000000000 : ℝ)+2*(44530029111/34810000000000 : ℝ)*(2957/20000 : ℝ))^(137/32 : ℝ) := by
    rw [show (34801370734612503179/34810000000000000000 : ℝ)+2*(44530029111/34810000000000 : ℝ)*(2957/20000 : ℝ)=(10001303724280559/10000000000000000 : ℝ) by norm_num, show 1+2*(27912424681767267/100000000000000000000 : ℝ)=(50027912424681767267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34801370734612503179/34810000000000000000 : ℝ)*(X 1 0+X 2 0)+(44530029111/34810000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34801370734612503179/34810000000000000000 : ℝ)) (alpha := (44530029111/34810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34801370734612503179/34810000000000000000 : ℝ)*(X 0 1+X 2 1)+(44530029111/34810000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34801370734612503179/34810000000000000000 : ℝ)) (alpha := (44530029111/34810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34801370734612503179/34810000000000000000 : ℝ)*(X 0 2+X 1 2)+(44530029111/34810000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (34801370734612503179/34810000000000000000 : ℝ)) (alpha := (44530029111/34810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987178539/5000000000 : ℝ)*X 0 0+(5408614813/10000000000 : ℝ)*X 0 1+(5246642397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347460559/10000000000 : ℝ)*X 1 0+(-2056825817/10000000000 : ℝ)*X 1 1+(1311660621/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347460723/10000000000 : ℝ)*X 2 0+(2623321191/5000000000 : ℝ)*X 2 1+(-411365147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152680947/5000000000 : ℝ)*X 0 0+(4133620781/10000000000 : ℝ)*X 0 1+(2241753817/5000000000 : ℝ)*X 0 2+(2152680947/5000000000 : ℝ)*X 1 0+(4133620781/10000000000 : ℝ)*X 1 1+(2241753817/5000000000 : ℝ)*X 1 2+(2152680947/5000000000 : ℝ)*X 2 0+(4133620781/10000000000 : ℝ)*X 2 1+(2241753817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-493592113/2500000000 : ℝ)*X 0 0+(5247227757/10000000000 : ℝ)*X 0 1+(169000827/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530536869/1000000000 : ℝ)*X 1 0+(-1895441791/10000000000 : ℝ)*X 1 1+(2704013219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305369071/10000000000 : ℝ)*X 2 0+(1081605253/2000000000 : ℝ)*X 2 1+(-1895441507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305386507/10000000000 : ℝ)*X 0 0+(56028041/125000000 : ℝ)*X 0 1+(4134891789/10000000000 : ℝ)*X 0 2+(4305386507/10000000000 : ℝ)*X 1 0+(56028041/125000000 : ℝ)*X 1 1+(4134891789/10000000000 : ℝ)*X 1 2+(4305386507/10000000000 : ℝ)*X 2 0+(56028041/125000000 : ℝ)*X 2 1+(4134891789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (964129783245566984613/139240000000000000000000000 : ℝ) := by norm_num
    linear_combination (35749251/2500000000000 : ℝ)*(base19) + (708158919/50000000000000 : ℝ)*(base23) + (108553329/100000000000000 : ℝ)*(lower2) + (169719143/100000000000000 : ℝ)*(upper3) + (39679553/25000000000000 : ℝ)*(upper5) + (2258013213093773/50000000000000 : ℝ)*(major0) + (2258013213093773/50000000000000 : ℝ)*(major1) + (2258013213093773/50000000000000 : ℝ)*(major2) + (6173921811645089/100000000000000 : ℝ)*(sp0) + (1234791062280717/20000000000000 : ℝ)*(sp1) + (6173955325055787/100000000000000 : ℝ)*(sp2) + (1429040223017933/50000000000000 : ℝ)*(sp3) + (34929728537/100000000000000 : ℝ)*(sp4) + (1929269741/12500000000000 : ℝ)*(sp7) + (1429047940096897/50000000000000 : ℝ)*(f.failure) + (49391653930989/800000000000 : ℝ)*(f.sum) + (1773887990929/1740500000000000000000000000 : ℝ)*base65 + (9405019972315395633/1740500000000000000000000000000000 : ℝ)*base68 + (3035663817942104367/1740500000000000000000000000000000 : ℝ)*base69 + (20550157971766895633/1740500000000000000000000000000000 : ℝ)*base72 + (18908251683291/3481000000000000000000000000 : ℝ)*base73 + (23861331754262604367/1740500000000000000000000000000000 : ℝ)*base75 + (11930592772399895633/1740500000000000000000000000000000 : ℝ)*base78 + (7124404501480604367/1740500000000000000000000000000000 : ℝ)*base79 + (12010042574741/3481000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1124667/250000000000000000000 : ℝ)*base89 + (1124667/250000000000000000000 : ℝ)*base91 + (1124667/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5651313786136510185155125623/870250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640434659/50000000000000 : ℝ)*(base19) + (2082908771/100000000000000 : ℝ)*(base23) + (9814013/10000000000000 : ℝ)*(upper3) + (29661307/25000000000000 : ℝ)*(lower4) + (144771511/100000000000000 : ℝ)*(upper5) + (2274471912049321/50000000000000 : ℝ)*(major0) + (2274471912049321/50000000000000 : ℝ)*(major1) + (2274471912049321/50000000000000 : ℝ)*(major2) + (14681211159/50000000000000 : ℝ)*(sp1) + (9194979689/20000000000000 : ℝ)*(sp2) + (3109479419611221/50000000000000 : ℝ)*(sp4) + (6218928195930807/100000000000000 : ℝ)*(sp5) + (6218910781415227/100000000000000 : ℝ)*(sp6) + (1439464296255803/50000000000000 : ℝ)*(sp7) + (1439464296255803/50000000000000 : ℝ)*(f.failure) + (3109479419611221/50000000000000 : ℝ)*(f.sum) + (8419908279887/1740500000000000000000000000 : ℝ)*base66 + (18649210023251291459/1740500000000000000000000000000000 : ℝ)*base67 + (21025004757291459/1740500000000000000000000000000000 : ℝ)*base69 + (2087299571291459/1740500000000000000000000000000000 : ℝ)*base71 + (6671316657227/3481000000000000000000000000 : ℝ)*base73 + (13075416483987708541/1740500000000000000000000000000000 : ℝ)*base76 + (9722899441541291459/1740500000000000000000000000000000 : ℝ)*base77 + (4342987390764208541/1740500000000000000000000000000000 : ℝ)*base80 + (367299687523/1740500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (164967/250000000000000000000 : ℝ)*base90 + (164967/250000000000000000000 : ℝ)*base92 + (164967/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1425_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1425_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1425_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1425_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
