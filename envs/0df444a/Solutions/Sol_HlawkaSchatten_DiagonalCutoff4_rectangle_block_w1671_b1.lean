-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1671_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:43.305658+00:00
-- url     : https://prove2.me/submissions/3c2bd65d-e795-4e73-84ee-ce1bb15f6797

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
theorem support_rectangle_w1671_s3_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-780984187/5000000000 : ℝ)*x 0 + (5441437541/10000000000 : ℝ)*x 1 + (5185078003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (780984187/5000000000 : ℝ)^5003 ≤ (9686411273459/100000000000000 : ℝ)^3979 := by
    have hnat : (780984187 : ℕ)^5003*100000000000000^3979 ≤ 9686411273459^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780984187 5000000000 9686411273459 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441437541/10000000000 : ℝ)^5003 ≤ (23263190194249/50000000000000 : ℝ)^3979 := by
    have hnat : (5441437541 : ℕ)^5003*50000000000000^3979 ≤ 23263190194249^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441437541 10000000000 23263190194249 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185078003/10000000000 : ℝ)^5003 ≤ (21893604157107/50000000000000 : ℝ)^3979 := by
    have hnat : (5185078003 : ℕ)^5003*50000000000000^3979 ≤ 21893604157107^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185078003 10000000000 21893604157107 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-780984187/5000000000 : ℝ), (5441437541/10000000000 : ℝ), (5185078003/10000000000 : ℝ)] ![(9686411273459/100000000000000 : ℝ), (23263190194249/50000000000000 : ℝ), (21893604157107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-780984187/5000000000 : ℝ)|^5003 ≤ (9686411273459/100000000000000 : ℝ)^3979
        have hw : |(-780984187/5000000000 : ℝ)|=(780984187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441437541/10000000000 : ℝ)|^5003 ≤ (23263190194249/50000000000000 : ℝ)^3979
        have hw : |(5441437541/10000000000 : ℝ)|=(5441437541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185078003/10000000000 : ℝ)|^5003 ≤ (21893604157107/50000000000000 : ℝ)^3979
        have hw : |(5185078003/10000000000 : ℝ)|=(5185078003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344557451/10000000000 : ℝ)*x 0 + (-1693833699/10000000000 : ℝ)*x 1 + (518507803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344557451/10000000000 : ℝ)^5003 ≤ (5685904410837/12500000000000 : ℝ)^3979 := by
    have hnat : (5344557451 : ℕ)^5003*12500000000000^3979 ≤ 5685904410837^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344557451 10000000000 5685904410837 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693833699/10000000000 : ℝ)^5003 ≤ (10725556088033/100000000000000 : ℝ)^3979 := by
    have hnat : (1693833699 : ℕ)^5003*100000000000000^3979 ≤ 10725556088033^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693833699 10000000000 10725556088033 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518507803/1000000000 : ℝ)^5003 ≤ (43787208600903/100000000000000 : ℝ)^3979 := by
    have hnat : (518507803 : ℕ)^5003*100000000000000^3979 ≤ 43787208600903^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518507803 1000000000 43787208600903 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344557451/10000000000 : ℝ), (-1693833699/10000000000 : ℝ), (518507803/1000000000 : ℝ)] ![(5685904410837/12500000000000 : ℝ), (10725556088033/100000000000000 : ℝ), (43787208600903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344557451/10000000000 : ℝ)|^5003 ≤ (5685904410837/12500000000000 : ℝ)^3979
        have hw : |(5344557451/10000000000 : ℝ)|=(5344557451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1693833699/10000000000 : ℝ)|^5003 ≤ (10725556088033/100000000000000 : ℝ)^3979
        have hw : |(-1693833699/10000000000 : ℝ)|=(1693833699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518507803/1000000000 : ℝ)|^5003 ≤ (43787208600903/100000000000000 : ℝ)^3979
        have hw : |(518507803/1000000000 : ℝ)|=(518507803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336139363/2500000000 : ℝ)*x 0 + (648134749/1250000000 : ℝ)*x 1 + (-423458437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336139363/2500000000 : ℝ)^5003 ≤ (45487235297397/100000000000000 : ℝ)^3979 := by
    have hnat : (1336139363 : ℕ)^5003*100000000000000^3979 ≤ 45487235297397^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336139363 2500000000 45487235297397 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648134749/1250000000 : ℝ)^5003 ≤ (21893604098707/50000000000000 : ℝ)^3979 := by
    have hnat : (648134749 : ℕ)^5003*50000000000000^3979 ≤ 21893604098707^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648134749 1250000000 21893604098707 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423458437/2500000000 : ℝ)^5003 ≤ (2681389119539/25000000000000 : ℝ)^3979 := by
    have hnat : (423458437 : ℕ)^5003*25000000000000^3979 ≤ 2681389119539^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423458437 2500000000 2681389119539 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336139363/2500000000 : ℝ), (648134749/1250000000 : ℝ), (-423458437/2500000000 : ℝ)] ![(45487235297397/100000000000000 : ℝ), (21893604098707/50000000000000 : ℝ), (2681389119539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336139363/2500000000 : ℝ)|^5003 ≤ (45487235297397/100000000000000 : ℝ)^3979
        have hw : |(1336139363/2500000000 : ℝ)|=(1336139363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648134749/1250000000 : ℝ)|^5003 ≤ (21893604098707/50000000000000 : ℝ)^3979
        have hw : |(648134749/1250000000 : ℝ)|=(648134749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423458437/2500000000 : ℝ)|^5003 ≤ (2681389119539/25000000000000 : ℝ)^3979
        have hw : |(-423458437/2500000000 : ℝ)|=(423458437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041229721/2500000000 : ℝ)*x 0 + (3834284841/10000000000 : ℝ)*x 1 + (22575647/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041229721/2500000000 : ℝ)^5003 ≤ (6648778612791/20000000000000 : ℝ)^3979 := by
    have hnat : (1041229721 : ℕ)^5003*20000000000000^3979 ≤ 6648778612791^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041229721 2500000000 6648778612791 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3834284841/10000000000 : ℝ)^5003 ≤ (5992045277937/20000000000000 : ℝ)^3979 := by
    have hnat : (3834284841 : ℕ)^5003*20000000000000^3979 ≤ 5992045277937^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3834284841 10000000000 5992045277937 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22575647/50000000 : ℝ)^5003 ≤ (3679588053383/10000000000000 : ℝ)^3979 := by
    have hnat : (22575647 : ℕ)^5003*10000000000000^3979 ≤ 3679588053383^3979*50000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22575647 50000000 3679588053383 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041229721/2500000000 : ℝ), (3834284841/10000000000 : ℝ), (22575647/50000000 : ℝ)] ![(6648778612791/20000000000000 : ℝ), (5992045277937/20000000000000 : ℝ), (3679588053383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041229721/2500000000 : ℝ)|^5003 ≤ (6648778612791/20000000000000 : ℝ)^3979
        have hw : |(1041229721/2500000000 : ℝ)|=(1041229721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3834284841/10000000000 : ℝ)|^5003 ≤ (5992045277937/20000000000000 : ℝ)^3979
        have hw : |(3834284841/10000000000 : ℝ)|=(3834284841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22575647/50000000 : ℝ)|^5003 ≤ (3679588053383/10000000000000 : ℝ)^3979
        have hw : |(22575647/50000000 : ℝ)|=(22575647/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390507477/2500000000 : ℝ)*x 0 + (324189747/625000000 : ℝ)*x 1 + (2719729471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390507477/2500000000 : ℝ)^5003 ≤ (9686891078251/100000000000000 : ℝ)^3979 := by
    have hnat : (390507477 : ℕ)^5003*100000000000000^3979 ≤ 9686891078251^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390507477 2500000000 9686891078251 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324189747/625000000 : ℝ)^5003 ≤ (43807999104691/100000000000000 : ℝ)^3979 := by
    have hnat : (324189747 : ℕ)^5003*100000000000000^3979 ≤ 43807999104691^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324189747 625000000 43807999104691 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719729471/5000000000 : ℝ)^5003 ≤ (23252554896587/50000000000000 : ℝ)^3979 := by
    have hnat : (2719729471 : ℕ)^5003*50000000000000^3979 ≤ 23252554896587^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719729471 5000000000 23252554896587 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390507477/2500000000 : ℝ), (324189747/625000000 : ℝ), (2719729471/5000000000 : ℝ)] ![(9686891078251/100000000000000 : ℝ), (43807999104691/100000000000000 : ℝ), (23252554896587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390507477/2500000000 : ℝ)|^5003 ≤ (9686891078251/100000000000000 : ℝ)^3979
        have hw : |(-390507477/2500000000 : ℝ)|=(390507477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324189747/625000000 : ℝ)|^5003 ≤ (43807999104691/100000000000000 : ℝ)^3979
        have hw : |(324189747/625000000 : ℝ)|=(324189747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719729471/5000000000 : ℝ)|^5003 ≤ (23252554896587/50000000000000 : ℝ)^3979
        have hw : |(2719729471/5000000000 : ℝ)|=(2719729471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055183881/2000000000 : ℝ)*x 0 + (-1439452793/10000000000 : ℝ)*x 1 + (5439458969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055183881/2000000000 : ℝ)^5003 ≤ (44753940343337/100000000000000 : ℝ)^3979 := by
    have hnat : (1055183881 : ℕ)^5003*100000000000000^3979 ≤ 44753940343337^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055183881 2000000000 44753940343337 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439452793/10000000000 : ℝ)^5003 ≤ (8740949561211/100000000000000 : ℝ)^3979 := by
    have hnat : (1439452793 : ℕ)^5003*100000000000000^3979 ≤ 8740949561211^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439452793 10000000000 8740949561211 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439458969/10000000000 : ℝ)^5003 ≤ (46505110083419/100000000000000 : ℝ)^3979 := by
    have hnat : (5439458969 : ℕ)^5003*100000000000000^3979 ≤ 46505110083419^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439458969 10000000000 46505110083419 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055183881/2000000000 : ℝ), (-1439452793/10000000000 : ℝ), (5439458969/10000000000 : ℝ)] ![(44753940343337/100000000000000 : ℝ), (8740949561211/100000000000000 : ℝ), (46505110083419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055183881/2000000000 : ℝ)|^5003 ≤ (44753940343337/100000000000000 : ℝ)^3979
        have hw : |(1055183881/2000000000 : ℝ)|=(1055183881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439452793/10000000000 : ℝ)|^5003 ≤ (8740949561211/100000000000000 : ℝ)^3979
        have hw : |(-1439452793/10000000000 : ℝ)|=(1439452793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439458969/10000000000 : ℝ)|^5003 ≤ (46505110083419/100000000000000 : ℝ)^3979
        have hw : |(5439458969/10000000000 : ℝ)|=(5439458969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659489931/1250000000 : ℝ)*x 0 + (271972947/500000000 : ℝ)*x 1 + (-1439452773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659489931/1250000000 : ℝ)^5003 ≤ (22376970400981/50000000000000 : ℝ)^3979 := by
    have hnat : (659489931 : ℕ)^5003*50000000000000^3979 ≤ 22376970400981^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659489931 1250000000 22376970400981 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271972947/500000000 : ℝ)^5003 ≤ (23252554885837/50000000000000 : ℝ)^3979 := by
    have hnat : (271972947 : ℕ)^5003*50000000000000^3979 ≤ 23252554885837^3979*500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271972947 500000000 23252554885837 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1439452773/10000000000 : ℝ)^5003 ≤ (2185237352127/25000000000000 : ℝ)^3979 := by
    have hnat : (1439452773 : ℕ)^5003*25000000000000^3979 ≤ 2185237352127^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439452773 10000000000 2185237352127 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659489931/1250000000 : ℝ), (271972947/500000000 : ℝ), (-1439452773/10000000000 : ℝ)] ![(22376970400981/50000000000000 : ℝ), (23252554885837/50000000000000 : ℝ), (2185237352127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659489931/1250000000 : ℝ)|^5003 ≤ (22376970400981/50000000000000 : ℝ)^3979
        have hw : |(659489931/1250000000 : ℝ)|=(659489931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271972947/500000000 : ℝ)|^5003 ≤ (23252554885837/50000000000000 : ℝ)^3979
        have hw : |(271972947/500000000 : ℝ)|=(271972947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1439452773/10000000000 : ℝ)|^5003 ≤ (2185237352127/25000000000000 : ℝ)^3979
        have hw : |(-1439452773/10000000000 : ℝ)|=(1439452773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s3_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165082261/10000000000 : ℝ)*x 0 + (4509929441/10000000000 : ℝ)*x 1 + (153581583/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165082261/10000000000 : ℝ)^5003 ≤ (16622766364243/50000000000000 : ℝ)^3979 := by
    have hnat : (4165082261 : ℕ)^5003*50000000000000^3979 ≤ 16622766364243^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165082261 10000000000 16622766364243 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509929441/10000000000 : ℝ)^5003 ≤ (18371302911587/50000000000000 : ℝ)^3979 := by
    have hnat : (4509929441 : ℕ)^5003*50000000000000^3979 ≤ 18371302911587^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509929441 10000000000 18371302911587 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153581583/400000000 : ℝ)^5003 ≤ (15005930718017/50000000000000 : ℝ)^3979 := by
    have hnat : (153581583 : ℕ)^5003*50000000000000^3979 ≤ 15005930718017^3979*400000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153581583 400000000 15005930718017 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165082261/10000000000 : ℝ), (4509929441/10000000000 : ℝ), (153581583/400000000 : ℝ)] ![(16622766364243/50000000000000 : ℝ), (18371302911587/50000000000000 : ℝ), (15005930718017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165082261/10000000000 : ℝ)|^5003 ≤ (16622766364243/50000000000000 : ℝ)^3979
        have hw : |(4165082261/10000000000 : ℝ)|=(4165082261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509929441/10000000000 : ℝ)|^5003 ≤ (18371302911587/50000000000000 : ℝ)^3979
        have hw : |(4509929441/10000000000 : ℝ)|=(4509929441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153581583/400000000 : ℝ)|^5003 ≤ (15005930718017/50000000000000 : ℝ)^3979
        have hw : |(153581583/400000000 : ℝ)|=(153581583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (407/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10771/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4057/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (407/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (407/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (407/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (407/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (407/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (407/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (429/4000 : ℝ) ^ (4999/1024 : ℝ) ≤ (115461904187979/6250000000000000000 : ℝ) := by
    have hpowers : (429/4000 : ℝ)^4999 ≤ (115461904187979/6250000000000000000 : ℝ)^1024 := by
      have hnat : (429 : ℕ)^4999*6250000000000000000^1024 ≤ 115461904187979^1024*4000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        429 4000 115461904187979 6250000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (429/4000 : ℝ)) (X := (115461904187979/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (407/2500 : ℝ) ^ (4999/1024 : ℝ) ≤ (2834367222997313/20000000000000000000 : ℝ) := by
    have hpowers : (407/2500 : ℝ)^4999 ≤ (2834367222997313/20000000000000000000 : ℝ)^1024 := by
      have hnat : (407 : ℕ)^4999*20000000000000000000^1024 ≤ 2834367222997313^1024*2500^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        407 2500 2834367222997313 20000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (407/2500 : ℝ)) (X := (2834367222997313/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125115461904187979/3125000000000000000 : ℝ) ≤ (80000605465109/80000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (3125115461904187979/3125000000000000000 : ℝ)^1024 ≤ (80000605465109/80000000000000 : ℝ)^4999 := by
      have hnat : (3125115461904187979 : ℕ)^1024*80000000000000^4999 ≤ 80000605465109^4999*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125115461904187979 3125000000000000000 80000605465109 80000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000605465109/80000000000000 : ℝ)) (X := (3125115461904187979/3125000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016019226581994229/100000000000000000000 : ℝ) ≤ (10000328118491357/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (100016019226581994229/100000000000000000000 : ℝ)^1024 ≤ (10000328118491357/10000000000000000 : ℝ)^4999 := by
      have hnat : (100016019226581994229 : ℕ)^1024*10000000000000000^4999 ≤ 10000328118491357^4999*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016019226581994229 100000000000000000000 10000328118491357 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000328118491357/10000000000000000 : ℝ)) (X := (100016019226581994229/100000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002834367222997313/10000000000000000000 : ℝ) ≤ (10000580553844089/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (10002834367222997313/10000000000000000000 : ℝ)^1024 ≤ (10000580553844089/10000000000000000 : ℝ)^4999 := by
      have hnat : (10002834367222997313 : ℕ)^1024*10000000000000000^4999 ≤ 10000580553844089^4999*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002834367222997313 10000000000000000000 10000580553844089 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000580553844089/10000000000000000 : ℝ)) (X := (10002834367222997313/10000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(115461904187979/6250000000000000000 : ℝ) ≤ ((201981838841887129/202000000000000000 : ℝ)+2*(63108838183/138875000000000 : ℝ)*(429/4000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (201981838841887129/202000000000000000 : ℝ)+2*(63108838183/138875000000000 : ℝ)*(429/4000 : ℝ)=(80000605465109/80000000000000 : ℝ) by norm_num, show 1+2*(115461904187979/6250000000000000000 : ℝ)=(3125115461904187979/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2834367222997313/20000000000000000000 : ℝ)+(115461904187979/6250000000000000000 : ℝ) ≤ ((201981838841887129/202000000000000000 : ℝ)+(63108838183/138875000000000 : ℝ)*((407/2500 : ℝ)+(429/4000 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (201981838841887129/202000000000000000 : ℝ)+(63108838183/138875000000000 : ℝ)*((407/2500 : ℝ)+(429/4000 : ℝ))=(10000328118491357/10000000000000000 : ℝ) by norm_num, show 1+(2834367222997313/20000000000000000000 : ℝ)+(115461904187979/6250000000000000000 : ℝ)=(100016019226581994229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2834367222997313/20000000000000000000 : ℝ) ≤ ((201981838841887129/202000000000000000 : ℝ)+2*(63108838183/138875000000000 : ℝ)*(407/2500 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (201981838841887129/202000000000000000 : ℝ)+2*(63108838183/138875000000000 : ℝ)*(407/2500 : ℝ)=(10000580553844089/10000000000000000 : ℝ) by norm_num, show 1+2*(2834367222997313/20000000000000000000 : ℝ)=(10002834367222997313/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (201981838841887129/202000000000000000 : ℝ)*(X 1 0+X 2 0)+(63108838183/138875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (407/2500 : ℝ)) (c := (201981838841887129/202000000000000000 : ℝ)) (alpha := (63108838183/138875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (201981838841887129/202000000000000000 : ℝ)*(X 0 1+X 2 1)+(63108838183/138875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (407/2500 : ℝ)) (c := (201981838841887129/202000000000000000 : ℝ)) (alpha := (63108838183/138875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (201981838841887129/202000000000000000 : ℝ)*(X 0 2+X 1 2)+(63108838183/138875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (407/2500 : ℝ)) (c := (201981838841887129/202000000000000000 : ℝ)) (alpha := (63108838183/138875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-780984187/5000000000 : ℝ)*X 0 0+(5441437541/10000000000 : ℝ)*X 0 1+(5185078003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344557451/10000000000 : ℝ)*X 1 0+(-1693833699/10000000000 : ℝ)*X 1 1+(518507803/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336139363/2500000000 : ℝ)*X 2 0+(648134749/1250000000 : ℝ)*X 2 1+(-423458437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1041229721/2500000000 : ℝ)*X 0 0+(3834284841/10000000000 : ℝ)*X 0 1+(22575647/50000000 : ℝ)*X 0 2+(1041229721/2500000000 : ℝ)*X 1 0+(3834284841/10000000000 : ℝ)*X 1 1+(22575647/50000000 : ℝ)*X 1 2+(1041229721/2500000000 : ℝ)*X 2 0+(3834284841/10000000000 : ℝ)*X 2 1+(22575647/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-390507477/2500000000 : ℝ)*X 0 0+(324189747/625000000 : ℝ)*X 0 1+(2719729471/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055183881/2000000000 : ℝ)*X 1 0+(-1439452793/10000000000 : ℝ)*X 1 1+(5439458969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659489931/1250000000 : ℝ)*X 2 0+(271972947/500000000 : ℝ)*X 2 1+(-1439452773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165082261/10000000000 : ℝ)*X 0 0+(4509929441/10000000000 : ℝ)*X 0 1+(153581583/400000000 : ℝ)*X 0 2+(4165082261/10000000000 : ℝ)*X 1 0+(4509929441/10000000000 : ℝ)*X 1 1+(153581583/400000000 : ℝ)*X 1 2+(4165082261/10000000000 : ℝ)*X 2 0+(4509929441/10000000000 : ℝ)*X 2 1+(153581583/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17881922621468476730793/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1091925859/100000000000000 : ℝ)*(base19) + (63515209/6250000000000 : ℝ)*(base23) + (8167807/20000000000000 : ℝ)*(lower2) + (192618677/100000000000000 : ℝ)*(upper3) + (19695053/20000000000000 : ℝ)*(upper5) + (67119688045487/2500000000000 : ℝ)*(major0) + (67119688045487/2500000000000 : ℝ)*(major1) + (67119688045487/2500000000000 : ℝ)*(major2) + (487598319347111/12500000000000 : ℝ)*(sp0) + (780159794559321/20000000000000 : ℝ)*(sp1) + (48759988105989/1250000000000 : ℝ)*(sp2) + (183596110586111/12500000000000 : ℝ)*(sp3) + (540397823/4000000000000 : ℝ)*(sp4) + (5855801967/100000000000000 : ℝ)*(sp7) + (293754948098171/20000000000000 : ℝ)*(f.failure) + (121900002022577/3125000000000 : ℝ)*(f.sum) + (15422210683/5000000000000000000000000 : ℝ)*base66 + (37229545645523/5000000000000000000000000000 : ℝ)*base67 + (19232518265523/5000000000000000000000000000 : ℝ)*base69 + (1098044790523/5000000000000000000000000000 : ℝ)*base71 + (728488647/312500000000000000000000 : ℝ)*base73 + (55459085523/5000000000000000000000000000 : ℝ)*base75 + (8587302865523/5000000000000000000000000000 : ℝ)*base77 + (47965234485523/5000000000000000000000000000 : ℝ)*base79 + (8920902173/5000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1634997/400000000000000000000 : ℝ)*base90 + (1634997/400000000000000000000 : ℝ)*base92 + (1634997/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16335412874747478576958881/4444000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25836357/5000000000000 : ℝ)*(base19) + (294859943/50000000000000 : ℝ)*(base23) + (10160657/12500000000000 : ℝ)*(upper3) + (7945511/50000000000000 : ℝ)*(lower4) + (77859709/100000000000000 : ℝ)*(upper5) + (109065471534589/4000000000000 : ℝ)*(major0) + (109065471534589/4000000000000 : ℝ)*(major1) + (109065471534589/4000000000000 : ℝ)*(major2) + (6488953471/100000000000000 : ℝ)*(sp1) + (7302569087/100000000000000 : ℝ)*(sp2) + (1980802055139651/50000000000000 : ℝ)*(sp4) + (990399276149673/25000000000000 : ℝ)*(sp5) + (396159621799033/10000000000000 : ℝ)*(sp6) + (1491669343922291/100000000000000 : ℝ)*(sp7) + (1491669343922291/100000000000000 : ℝ)*(f.failure) + (1980802055139651/50000000000000 : ℝ)*(f.sum) + (4938474965563/1111000000000000000000000000 : ℝ)*base65 + (51821180906566791/8888000000000000000000000000000 : ℝ)*base67 + (50229784737654791/8888000000000000000000000000000 : ℝ)*base69 + (62239465222830791/8888000000000000000000000000000 : ℝ)*base71 + (1701821114871/555500000000000000000000000 : ℝ)*base73 + (22339310117382791/8888000000000000000000000000000 : ℝ)*base75 + (11508152345926791/8888000000000000000000000000000 : ℝ)*base77 + (5782958522566791/8888000000000000000000000000000 : ℝ)*base79 + (5047222507499/1111000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8619837/2000000000000000000000 : ℝ)*base90 + (8619837/2000000000000000000000 : ℝ)*base92 + (8619837/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1671_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (407/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10771/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1671_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1671_s4_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1561995453/10000000000 : ℝ)*x 0 + (1360324377/2500000000 : ℝ)*x 1 + (5185199901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1561995453/10000000000 : ℝ)^5003 ≤ (968662241847/10000000000000 : ℝ)^3979 := by
    have hnat : (1561995453 : ℕ)^5003*10000000000000^3979 ≤ 968662241847^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561995453 10000000000 968662241847 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360324377/2500000000 : ℝ)^5003 ≤ (9304974984371/20000000000000 : ℝ)^3979 := by
    have hnat : (1360324377 : ℕ)^5003*20000000000000^3979 ≤ 9304974984371^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360324377 2500000000 9304974984371 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185199901/10000000000 : ℝ)^5003 ≤ (10947125662099/25000000000000 : ℝ)^3979 := by
    have hnat : (5185199901 : ℕ)^5003*25000000000000^3979 ≤ 10947125662099^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185199901 10000000000 10947125662099 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1561995453/10000000000 : ℝ), (1360324377/2500000000 : ℝ), (5185199901/10000000000 : ℝ)] ![(968662241847/10000000000000 : ℝ), (9304974984371/20000000000000 : ℝ), (10947125662099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1561995453/10000000000 : ℝ)|^5003 ≤ (968662241847/10000000000000 : ℝ)^3979
        have hw : |(-1561995453/10000000000 : ℝ)|=(1561995453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360324377/2500000000 : ℝ)|^5003 ≤ (9304974984371/20000000000000 : ℝ)^3979
        have hw : |(1360324377/2500000000 : ℝ)|=(1360324377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185199901/10000000000 : ℝ)|^5003 ≤ (10947125662099/25000000000000 : ℝ)^3979
        have hw : |(5185199901/10000000000 : ℝ)|=(5185199901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344519551/10000000000 : ℝ)*x 0 + (-1693722039/10000000000 : ℝ)*x 1 + (5185199951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344519551/10000000000 : ℝ)^5003 ≤ (9097365941967/20000000000000 : ℝ)^3979 := by
    have hnat : (5344519551 : ℕ)^5003*20000000000000^3979 ≤ 9097365941967^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344519551 10000000000 9097365941967 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693722039/10000000000 : ℝ)^5003 ≤ (5362333546277/50000000000000 : ℝ)^3979 := by
    have hnat : (1693722039 : ℕ)^5003*50000000000000^3979 ≤ 5362333546277^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693722039 10000000000 5362333546277 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185199951/10000000000 : ℝ)^5003 ≤ (21894251589653/50000000000000 : ℝ)^3979 := by
    have hnat : (5185199951 : ℕ)^5003*50000000000000^3979 ≤ 21894251589653^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185199951 10000000000 21894251589653 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344519551/10000000000 : ℝ), (-1693722039/10000000000 : ℝ), (5185199951/10000000000 : ℝ)] ![(9097365941967/20000000000000 : ℝ), (5362333546277/50000000000000 : ℝ), (21894251589653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344519551/10000000000 : ℝ)|^5003 ≤ (9097365941967/20000000000000 : ℝ)^3979
        have hw : |(5344519551/10000000000 : ℝ)|=(5344519551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1693722039/10000000000 : ℝ)|^5003 ≤ (5362333546277/50000000000000 : ℝ)^3979
        have hw : |(-1693722039/10000000000 : ℝ)|=(1693722039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185199951/10000000000 : ℝ)|^5003 ≤ (21894251589653/50000000000000 : ℝ)^3979
        have hw : |(5185199951/10000000000 : ℝ)|=(5185199951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344518583/10000000000 : ℝ)*x 0 + (2592600279/5000000000 : ℝ)*x 1 + (-423430633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344518583/10000000000 : ℝ)^5003 ≤ (5685852418881/12500000000000 : ℝ)^3979 := by
    have hnat : (5344518583 : ℕ)^5003*12500000000000^3979 ≤ 5685852418881^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344518583 10000000000 5685852418881 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592600279/5000000000 : ℝ)^5003 ≤ (21894254812279/50000000000000 : ℝ)^3979 := by
    have hnat : (2592600279 : ℕ)^5003*50000000000000^3979 ≤ 21894254812279^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592600279 5000000000 21894254812279 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423430633/2500000000 : ℝ)^5003 ≤ (2681167754401/25000000000000 : ℝ)^3979 := by
    have hnat : (423430633 : ℕ)^5003*25000000000000^3979 ≤ 2681167754401^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423430633 2500000000 2681167754401 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344518583/10000000000 : ℝ), (2592600279/5000000000 : ℝ), (-423430633/2500000000 : ℝ)] ![(5685852418881/12500000000000 : ℝ), (21894254812279/50000000000000 : ℝ), (2681167754401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344518583/10000000000 : ℝ)|^5003 ≤ (5685852418881/12500000000000 : ℝ)^3979
        have hw : |(5344518583/10000000000 : ℝ)|=(5344518583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592600279/5000000000 : ℝ)|^5003 ≤ (21894254812279/50000000000000 : ℝ)^3979
        have hw : |(2592600279/5000000000 : ℝ)|=(2592600279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423430633/2500000000 : ℝ)|^5003 ≤ (2681167754401/25000000000000 : ℝ)^3979
        have hw : |(-423430633/2500000000 : ℝ)|=(423430633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082468691/5000000000 : ℝ)*x 0 + (958657359/2500000000 : ℝ)*x 1 + (2257390437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082468691/5000000000 : ℝ)^5003 ≤ (831101967763/2500000000000 : ℝ)^3979 := by
    have hnat : (2082468691 : ℕ)^5003*2500000000000^3979 ≤ 831101967763^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082468691 5000000000 831101967763 2500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958657359/2500000000 : ℝ)^5003 ≤ (936362873613/3125000000000 : ℝ)^3979 := by
    have hnat : (958657359 : ℕ)^5003*3125000000000^3979 ≤ 936362873613^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958657359 2500000000 936362873613 3125000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257390437/5000000000 : ℝ)^5003 ≤ (574879833051/1562500000000 : ℝ)^3979 := by
    have hnat : (2257390437 : ℕ)^5003*1562500000000^3979 ≤ 574879833051^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257390437 5000000000 574879833051 1562500000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082468691/5000000000 : ℝ), (958657359/2500000000 : ℝ), (2257390437/5000000000 : ℝ)] ![(831101967763/2500000000000 : ℝ), (936362873613/3125000000000 : ℝ), (574879833051/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082468691/5000000000 : ℝ)|^5003 ≤ (831101967763/2500000000000 : ℝ)^3979
        have hw : |(2082468691/5000000000 : ℝ)|=(2082468691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958657359/2500000000 : ℝ)|^5003 ≤ (936362873613/3125000000000 : ℝ)^3979
        have hw : |(958657359/2500000000 : ℝ)|=(958657359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257390437/5000000000 : ℝ)|^5003 ≤ (574879833051/1562500000000 : ℝ)^3979
        have hw : |(2257390437/5000000000 : ℝ)|=(2257390437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4881431/31250000 : ℝ)*x 0 + (2593576817/5000000000 : ℝ)*x 1 + (1359830593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4881431/31250000 : ℝ)^5003 ≤ (242177737511/2500000000000 : ℝ)^3979 := by
    have hnat : (4881431 : ℕ)^5003*2500000000000^3979 ≤ 242177737511^3979*31250000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881431 31250000 242177737511 2500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593576817/5000000000 : ℝ)^5003 ≤ (21904624396967/50000000000000 : ℝ)^3979 := by
    have hnat : (2593576817 : ℕ)^5003*50000000000000^3979 ≤ 21904624396967^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593576817 5000000000 21904624396967 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359830593/2500000000 : ℝ)^5003 ≤ (23251820846921/50000000000000 : ℝ)^3979 := by
    have hnat : (1359830593 : ℕ)^5003*50000000000000^3979 ≤ 23251820846921^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359830593 2500000000 23251820846921 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4881431/31250000 : ℝ), (2593576817/5000000000 : ℝ), (1359830593/2500000000 : ℝ)] ![(242177737511/2500000000000 : ℝ), (21904624396967/50000000000000 : ℝ), (23251820846921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4881431/31250000 : ℝ)|^5003 ≤ (242177737511/2500000000000 : ℝ)^3979
        have hw : |(-4881431/31250000 : ℝ)|=(4881431/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593576817/5000000000 : ℝ)|^5003 ≤ (21904624396967/50000000000000 : ℝ)^3979
        have hw : |(2593576817/5000000000 : ℝ)|=(2593576817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359830593/2500000000 : ℝ)|^5003 ≤ (23251820846921/50000000000000 : ℝ)^3979
        have hw : |(1359830593/2500000000 : ℝ)|=(1359830593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055190221/2000000000 : ℝ)*x 0 + (-287920093/2000000000 : ℝ)*x 1 + (543932263/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055190221/2000000000 : ℝ)^5003 ≤ (22377139223271/50000000000000 : ℝ)^3979 := by
    have hnat : (1055190221 : ℕ)^5003*50000000000000^3979 ≤ 22377139223271^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055190221 2000000000 22377139223271 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287920093/2000000000 : ℝ)^5003 ≤ (8742077074427/100000000000000 : ℝ)^3979 := by
    have hnat : (287920093 : ℕ)^5003*100000000000000^3979 ≤ 8742077074427^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287920093 2000000000 8742077074427 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543932263/1000000000 : ℝ)^5003 ≤ (581295555841/1250000000000 : ℝ)^3979 := by
    have hnat : (543932263 : ℕ)^5003*1250000000000^3979 ≤ 581295555841^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543932263 1000000000 581295555841 1250000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055190221/2000000000 : ℝ), (-287920093/2000000000 : ℝ), (543932263/1000000000 : ℝ)] ![(22377139223271/50000000000000 : ℝ), (8742077074427/100000000000000 : ℝ), (581295555841/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055190221/2000000000 : ℝ)|^5003 ≤ (22377139223271/50000000000000 : ℝ)^3979
        have hw : |(1055190221/2000000000 : ℝ)|=(1055190221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287920093/2000000000 : ℝ)|^5003 ≤ (8742077074427/100000000000000 : ℝ)^3979
        have hw : |(-287920093/2000000000 : ℝ)|=(287920093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543932263/1000000000 : ℝ)|^5003 ≤ (581295555841/1250000000000 : ℝ)^3979
        have hw : |(543932263/1000000000 : ℝ)|=(543932263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275951407/10000000000 : ℝ)*x 0 + (679915291/1250000000 : ℝ)*x 1 + (-1439600469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275951407/10000000000 : ℝ)^5003 ≤ (4475428166759/10000000000000 : ℝ)^3979 := by
    have hnat : (5275951407 : ℕ)^5003*10000000000000^3979 ≤ 4475428166759^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275951407 10000000000 4475428166759 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679915291/1250000000 : ℝ)^5003 ≤ (11625910305213/25000000000000 : ℝ)^3979 := by
    have hnat : (679915291 : ℕ)^5003*25000000000000^3979 ≤ 11625910305213^3979*1250000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679915291 1250000000 11625910305213 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1439600469/10000000000 : ℝ)^5003 ≤ (1092759638121/12500000000000 : ℝ)^3979 := by
    have hnat : (1439600469 : ℕ)^5003*12500000000000^3979 ≤ 1092759638121^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439600469 10000000000 1092759638121 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275951407/10000000000 : ℝ), (679915291/1250000000 : ℝ), (-1439600469/10000000000 : ℝ)] ![(4475428166759/10000000000000 : ℝ), (11625910305213/25000000000000 : ℝ), (1092759638121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275951407/10000000000 : ℝ)|^5003 ≤ (4475428166759/10000000000000 : ℝ)^3979
        have hw : |(5275951407/10000000000 : ℝ)|=(5275951407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679915291/1250000000 : ℝ)|^5003 ≤ (11625910305213/25000000000000 : ℝ)^3979
        have hw : |(679915291/1250000000 : ℝ)|=(679915291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1439600469/10000000000 : ℝ)|^5003 ≤ (1092759638121/12500000000000 : ℝ)^3979
        have hw : |(-1439600469/10000000000 : ℝ)|=(1439600469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_s4_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165099833/10000000000 : ℝ)*x 0 + (281849387/625000000 : ℝ)*x 1 + (3839875217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165099833/10000000000 : ℝ)^5003 ≤ (16622854541729/50000000000000 : ℝ)^3979 := by
    have hnat : (4165099833 : ℕ)^5003*50000000000000^3979 ≤ 16622854541729^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165099833 10000000000 16622854541729 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281849387/625000000 : ℝ)^5003 ≤ (36739130692479/100000000000000 : ℝ)^3979 := by
    have hnat : (281849387 : ℕ)^5003*100000000000000^3979 ≤ 36739130692479^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281849387 625000000 36739130692479 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3839875217/10000000000 : ℝ)^5003 ≤ (15007580101107/50000000000000 : ℝ)^3979 := by
    have hnat : (3839875217 : ℕ)^5003*50000000000000^3979 ≤ 15007580101107^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3839875217 10000000000 15007580101107 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165099833/10000000000 : ℝ), (281849387/625000000 : ℝ), (3839875217/10000000000 : ℝ)] ![(16622854541729/50000000000000 : ℝ), (36739130692479/100000000000000 : ℝ), (15007580101107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165099833/10000000000 : ℝ)|^5003 ≤ (16622854541729/50000000000000 : ℝ)^3979
        have hw : |(4165099833/10000000000 : ℝ)|=(4165099833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281849387/625000000 : ℝ)|^5003 ≤ (36739130692479/100000000000000 : ℝ)^3979
        have hw : |(281849387/625000000 : ℝ)|=(281849387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3839875217/10000000000 : ℝ)|^5003 ≤ (15007580101107/50000000000000 : ℝ)^3979
        have hw : |(3839875217/10000000000 : ℝ)|=(3839875217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10771/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5387/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (649/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10771/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10771/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10771/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10771/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10771/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10771/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10771/100000 : ℝ) ^ (4999/1024 : ℝ) ≤ (943197613504977/50000000000000000000 : ℝ) := by
    have hpowers : (10771/100000 : ℝ)^4999 ≤ (943197613504977/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10771 : ℕ)^4999*50000000000000000000^1024 ≤ 943197613504977^1024*100000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10771 100000 943197613504977 50000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10771/100000 : ℝ)) (X := (943197613504977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4057/25000 : ℝ) ^ (4999/1024 : ℝ) ≤ (3488054803491687/25000000000000000000 : ℝ) := by
    have hpowers : (4057/25000 : ℝ)^4999 ≤ (3488054803491687/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4057 : ℕ)^4999*25000000000000000000^1024 ≤ 3488054803491687^1024*25000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4057 25000 3488054803491687 25000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4057/25000 : ℝ)) (X := (3488054803491687/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000943197613504977/25000000000000000000 : ℝ) ≤ (2000015456209149/2000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (25000943197613504977/25000000000000000000 : ℝ)^1024 ≤ (2000015456209149/2000000000000000 : ℝ)^4999 := by
      have hnat : (25000943197613504977 : ℕ)^1024*2000000000000000^4999 ≤ 2000015456209149^4999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000943197613504977 25000000000000000000 2000015456209149 2000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000015456209149/2000000000000000 : ℝ)) (X := (25000943197613504977/25000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007919307220488351/50000000000000000000 : ℝ) ≤ (10000324419283309/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (50007919307220488351/50000000000000000000 : ℝ)^1024 ≤ (10000324419283309/10000000000000000 : ℝ)^4999 := by
      have hnat : (50007919307220488351 : ℕ)^1024*10000000000000000^4999 ≤ 10000324419283309^4999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007919307220488351 50000000000000000000 10000324419283309 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000324419283309/10000000000000000 : ℝ)) (X := (50007919307220488351/50000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503488054803491687/12500000000000000000 : ℝ) ≤ (10000571557520873/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (12503488054803491687/12500000000000000000 : ℝ)^1024 ≤ (10000571557520873/10000000000000000 : ℝ)^4999 := by
      have hnat : (12503488054803491687 : ℕ)^1024*10000000000000000^4999 ≤ 10000571557520873^4999*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503488054803491687 12500000000000000000 10000571557520873 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000571557520873/10000000000000000 : ℝ)) (X := (12503488054803491687/12500000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(943197613504977/50000000000000000000 : ℝ) ≤ ((54565097870753026777/54570000000000000000 : ℝ)+2*(61784559391/136425000000000 : ℝ)*(10771/100000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (54565097870753026777/54570000000000000000 : ℝ)+2*(61784559391/136425000000000 : ℝ)*(10771/100000 : ℝ)=(2000015456209149/2000000000000000 : ℝ) by norm_num, show 1+2*(943197613504977/50000000000000000000 : ℝ)=(25000943197613504977/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3488054803491687/25000000000000000000 : ℝ)+(943197613504977/50000000000000000000 : ℝ) ≤ ((54565097870753026777/54570000000000000000 : ℝ)+(61784559391/136425000000000 : ℝ)*((4057/25000 : ℝ)+(10771/100000 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (54565097870753026777/54570000000000000000 : ℝ)+(61784559391/136425000000000 : ℝ)*((4057/25000 : ℝ)+(10771/100000 : ℝ))=(10000324419283309/10000000000000000 : ℝ) by norm_num, show 1+(3488054803491687/25000000000000000000 : ℝ)+(943197613504977/50000000000000000000 : ℝ)=(50007919307220488351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3488054803491687/25000000000000000000 : ℝ) ≤ ((54565097870753026777/54570000000000000000 : ℝ)+2*(61784559391/136425000000000 : ℝ)*(4057/25000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (54565097870753026777/54570000000000000000 : ℝ)+2*(61784559391/136425000000000 : ℝ)*(4057/25000 : ℝ)=(10000571557520873/10000000000000000 : ℝ) by norm_num, show 1+2*(3488054803491687/25000000000000000000 : ℝ)=(12503488054803491687/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54565097870753026777/54570000000000000000 : ℝ)*(X 1 0+X 2 0)+(61784559391/136425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (10771/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54565097870753026777/54570000000000000000 : ℝ)) (alpha := (61784559391/136425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54565097870753026777/54570000000000000000 : ℝ)*(X 0 1+X 2 1)+(61784559391/136425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (10771/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54565097870753026777/54570000000000000000 : ℝ)) (alpha := (61784559391/136425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54565097870753026777/54570000000000000000 : ℝ)*(X 0 2+X 1 2)+(61784559391/136425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (10771/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54565097870753026777/54570000000000000000 : ℝ)) (alpha := (61784559391/136425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1561995453/10000000000 : ℝ)*X 0 0+(1360324377/2500000000 : ℝ)*X 0 1+(5185199901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344519551/10000000000 : ℝ)*X 1 0+(-1693722039/10000000000 : ℝ)*X 1 1+(5185199951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344518583/10000000000 : ℝ)*X 2 0+(2592600279/5000000000 : ℝ)*X 2 1+(-423430633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2082468691/5000000000 : ℝ)*X 0 0+(958657359/2500000000 : ℝ)*X 0 1+(2257390437/5000000000 : ℝ)*X 0 2+(2082468691/5000000000 : ℝ)*X 1 0+(958657359/2500000000 : ℝ)*X 1 1+(2257390437/5000000000 : ℝ)*X 1 2+(2082468691/5000000000 : ℝ)*X 2 0+(958657359/2500000000 : ℝ)*X 2 1+(2257390437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4881431/31250000 : ℝ)*X 0 0+(2593576817/5000000000 : ℝ)*X 0 1+(1359830593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055190221/2000000000 : ℝ)*X 1 0+(-287920093/2000000000 : ℝ)*X 1 1+(543932263/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275951407/10000000000 : ℝ)*X 2 0+(679915291/1250000000 : ℝ)*X 2 1+(-1439600469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165099833/10000000000 : ℝ)*X 0 0+(281849387/625000000 : ℝ)*X 0 1+(3839875217/10000000000 : ℝ)*X 0 2+(4165099833/10000000000 : ℝ)*X 1 0+(281849387/625000000 : ℝ)*X 1 1+(3839875217/10000000000 : ℝ)*X 1 2+(4165099833/10000000000 : ℝ)*X 2 0+(281849387/625000000 : ℝ)*X 2 1+(3839875217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296953459184150567330886843/90950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374624961/100000000000000 : ℝ)*(base19) + (47598753/100000000000000 : ℝ)*(base23) + (136910637/100000000000000 : ℝ)*(lower2) + (340114339/100000000000000 : ℝ)*(lower4) + (53294953/25000000000000 : ℝ)*(lower5) + (268753236130353/10000000000000 : ℝ)*(major0) + (268753236130353/10000000000000 : ℝ)*(major1) + (268753236130353/10000000000000 : ℝ)*(major2) + (30506096714949/781250000000 : ℝ)*(sp0) + (390478787111017/10000000000000 : ℝ)*(sp1) + (1952394099068189/50000000000000 : ℝ)*(sp2) + (1470268782972961/100000000000000 : ℝ)*(sp3) + (7866221659/100000000000000 : ℝ)*(sp4) + (1517012999/20000000000000 : ℝ)*(sp7) + (367569092009489/25000000000000 : ℝ)*(f.failure) + (390478824573513/10000000000000 : ℝ)*(f.sum) + (4390419322051/1819000000000000000000000000 : ℝ)*base66 + (3035648343687312573/181900000000000000000000000000000 : ℝ)*base68 + (2188667852266212573/181900000000000000000000000000000 : ℝ)*base70 + (2327222784486412573/181900000000000000000000000000000 : ℝ)*base72 + (1150312909893/909500000000000000000000000 : ℝ)*base74 + (3543346319741212573/181900000000000000000000000000000 : ℝ)*base76 + (3518554770744012573/181900000000000000000000000000000 : ℝ)*base78 + (2669722358697112573/181900000000000000000000000000000 : ℝ)*base80 + (722487920401/1819000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6693377/500000000000000000000 : ℝ)*base89 + (6693377/500000000000000000000 : ℝ)*base91 + (6693377/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14198844643649534600763/4547500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13277961/5000000000000 : ℝ)*(base19) + (289119809/50000000000000 : ℝ)*(base23) + (32569651/25000000000000 : ℝ)*(lower1) + (31782723/100000000000000 : ℝ)*(upper2) + (93146681/100000000000000 : ℝ)*(upper3) + (23654581/50000000000000 : ℝ)*(upper5) + (1364690994715293/50000000000000 : ℝ)*(major0) + (1364690994715293/50000000000000 : ℝ)*(major1) + (1364690994715293/50000000000000 : ℝ)*(major2) + (978970203/50000000000000 : ℝ)*(sp2) + (1982796352751053/50000000000000 : ℝ)*(sp4) + (1982796219971443/50000000000000 : ℝ)*(sp5) + (1982795084661041/50000000000000 : ℝ)*(sp6) + (746585584640517/50000000000000 : ℝ)*(sp7) + (746585584640517/50000000000000 : ℝ)*(f.failure) + (1982796352751053/50000000000000 : ℝ)*(f.sum) + (16144203157511/4547500000000000000000000000 : ℝ)*base66 + (6306233102327866887/909500000000000000000000000000000 : ℝ)*base67 + (13694288609613133113/909500000000000000000000000000000 : ℝ)*base70 + (3940546640437866887/909500000000000000000000000000000 : ℝ)*base71 + (19465046815529/4547500000000000000000000000 : ℝ)*base73 + (7389993632919133113/909500000000000000000000000000000 : ℝ)*base76 + (1069929825261133113/909500000000000000000000000000000 : ℝ)*base78 + (817000204047866887/909500000000000000000000000000000 : ℝ)*base79 + (50767571813/568437500000000000000000000 : ℝ)*base81 + (3894219/1000000000000000000000 : ℝ)*base90 + (3894219/1000000000000000000000 : ℝ)*base92 + (3894219/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1671_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10771/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (649/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1671_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1671_box_0 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1311315399/10000000000 : ℝ)*x 0 + (1350737097/2500000000 : ℝ)*x 1 + (5402948507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311315399/10000000000 : ℝ)^5003 ≤ (1554812882267/20000000000000 : ℝ)^3979 := by
    have hnat : (1311315399 : ℕ)^5003*20000000000000^3979 ≤ 1554812882267^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311315399 10000000000 1554812882267 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350737097/2500000000 : ℝ)^5003 ≤ (46112967148553/100000000000000 : ℝ)^3979 := by
    have hnat : (1350737097 : ℕ)^5003*100000000000000^3979 ≤ 46112967148553^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350737097 2500000000 46112967148553 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402948507/10000000000 : ℝ)^5003 ≤ (46112968425567/100000000000000 : ℝ)^3979 := by
    have hnat : (5402948507 : ℕ)^5003*100000000000000^3979 ≤ 46112968425567^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402948507 10000000000 46112968425567 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1311315399/10000000000 : ℝ), (1350737097/2500000000 : ℝ), (5402948507/10000000000 : ℝ)] ![(1554812882267/20000000000000 : ℝ), (46112967148553/100000000000000 : ℝ), (46112968425567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1311315399/10000000000 : ℝ)|^5003 ≤ (1554812882267/20000000000000 : ℝ)^3979
        have hw : |(-1311315399/10000000000 : ℝ)|=(1311315399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350737097/2500000000 : ℝ)|^5003 ≤ (46112967148553/100000000000000 : ℝ)^3979
        have hw : |(1350737097/2500000000 : ℝ)|=(1350737097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402948507/10000000000 : ℝ)|^5003 ≤ (46112968425567/100000000000000 : ℝ)^3979
        have hw : |(5402948507/10000000000 : ℝ)|=(5402948507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_1 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625332181/5000000000 : ℝ)*x 0 + (-381354889/2500000000 : ℝ)*x 1 + (1080589659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625332181/5000000000 : ℝ)^5003 ≤ (695074117819/1562500000000 : ℝ)^3979 := by
    have hnat : (2625332181 : ℕ)^5003*1562500000000^3979 ≤ 695074117819^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625332181 5000000000 695074117819 1562500000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381354889/2500000000 : ℝ)^5003 ≤ (2350572573913/25000000000000 : ℝ)^3979 := by
    have hnat : (381354889 : ℕ)^5003*25000000000000^3979 ≤ 2350572573913^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381354889 2500000000 2350572573913 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080589659/2000000000 : ℝ)^5003 ≤ (922259323011/2000000000000 : ℝ)^3979 := by
    have hnat : (1080589659 : ℕ)^5003*2000000000000^3979 ≤ 922259323011^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080589659 2000000000 922259323011 2000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625332181/5000000000 : ℝ), (-381354889/2500000000 : ℝ), (1080589659/2000000000 : ℝ)] ![(695074117819/1562500000000 : ℝ), (2350572573913/25000000000000 : ℝ), (922259323011/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625332181/5000000000 : ℝ)|^5003 ≤ (695074117819/1562500000000 : ℝ)^3979
        have hw : |(2625332181/5000000000 : ℝ)|=(2625332181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381354889/2500000000 : ℝ)|^5003 ≤ (2350572573913/25000000000000 : ℝ)^3979
        have hw : |(-381354889/2500000000 : ℝ)|=(381354889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080589659/2000000000 : ℝ)|^5003 ≤ (922259323011/2000000000000 : ℝ)^3979
        have hw : |(1080589659/2000000000 : ℝ)|=(1080589659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_2 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328166509/625000000 : ℝ)*x 0 + (1350737119/2500000000 : ℝ)*x 1 + (-305083921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328166509/625000000 : ℝ)^5003 ≤ (44484741218161/100000000000000 : ℝ)^3979 := by
    have hnat : (328166509 : ℕ)^5003*100000000000000^3979 ≤ 44484741218161^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328166509 625000000 44484741218161 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350737119/2500000000 : ℝ)^5003 ≤ (46112968092899/100000000000000 : ℝ)^3979 := by
    have hnat : (1350737119 : ℕ)^5003*100000000000000^3979 ≤ 46112968092899^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350737119 2500000000 46112968092899 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305083921/2000000000 : ℝ)^5003 ≤ (9402290675401/100000000000000 : ℝ)^3979 := by
    have hnat : (305083921 : ℕ)^5003*100000000000000^3979 ≤ 9402290675401^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305083921 2000000000 9402290675401 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328166509/625000000 : ℝ), (1350737119/2500000000 : ℝ), (-305083921/2000000000 : ℝ)] ![(44484741218161/100000000000000 : ℝ), (46112968092899/100000000000000 : ℝ), (9402290675401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328166509/625000000 : ℝ)|^5003 ≤ (44484741218161/100000000000000 : ℝ)^3979
        have hw : |(328166509/625000000 : ℝ)|=(328166509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350737119/2500000000 : ℝ)|^5003 ≤ (46112968092899/100000000000000 : ℝ)^3979
        have hw : |(1350737119/2500000000 : ℝ)|=(1350737119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305083921/2000000000 : ℝ)|^5003 ≤ (9402290675401/100000000000000 : ℝ)^3979
        have hw : |(-305083921/2000000000 : ℝ)|=(305083921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_3 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (444043407/1000000000 : ℝ)*x 0 + (1009720221/2500000000 : ℝ)*x 1 + (2019440279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444043407/1000000000 : ℝ)^5003 ≤ (36032133190171/100000000000000 : ℝ)^3979 := by
    have hnat : (444043407 : ℕ)^5003*100000000000000^3979 ≤ 36032133190171^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444043407 1000000000 36032133190171 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009720221/2500000000 : ℝ)^5003 ≤ (31983935023053/100000000000000 : ℝ)^3979 := by
    have hnat : (1009720221 : ℕ)^5003*100000000000000^3979 ≤ 31983935023053^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009720221 2500000000 31983935023053 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019440279/5000000000 : ℝ)^5003 ≤ (799598294427/2500000000000 : ℝ)^3979 := by
    have hnat : (2019440279 : ℕ)^5003*2500000000000^3979 ≤ 799598294427^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019440279 5000000000 799598294427 2500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(444043407/1000000000 : ℝ), (1009720221/2500000000 : ℝ), (2019440279/5000000000 : ℝ)] ![(36032133190171/100000000000000 : ℝ), (31983935023053/100000000000000 : ℝ), (799598294427/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(444043407/1000000000 : ℝ)|^5003 ≤ (36032133190171/100000000000000 : ℝ)^3979
        have hw : |(444043407/1000000000 : ℝ)|=(444043407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009720221/2500000000 : ℝ)|^5003 ≤ (31983935023053/100000000000000 : ℝ)^3979
        have hw : |(1009720221/2500000000 : ℝ)|=(1009720221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2019440279/5000000000 : ℝ)|^5003 ≤ (799598294427/2500000000000 : ℝ)^3979
        have hw : |(2019440279/5000000000 : ℝ)|=(2019440279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_4 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-113949961/625000000 : ℝ)*x 0 + (163004333/312500000 : ℝ)*x 1 + (5216138627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113949961/625000000 : ℝ)^5003 ≤ (94123705089/800000000000 : ℝ)^3979 := by
    have hnat : (113949961 : ℕ)^5003*800000000000^3979 ≤ 94123705089^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113949961 625000000 94123705089 800000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163004333/312500000 : ℝ)^5003 ≤ (11029317145287/25000000000000 : ℝ)^3979 := by
    have hnat : (163004333 : ℕ)^5003*25000000000000^3979 ≤ 11029317145287^3979*312500000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163004333 312500000 11029317145287 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216138627/10000000000 : ℝ)^5003 ≤ (44117268272749/100000000000000 : ℝ)^3979 := by
    have hnat : (5216138627 : ℕ)^5003*100000000000000^3979 ≤ 44117268272749^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216138627 10000000000 44117268272749 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113949961/625000000 : ℝ), (163004333/312500000 : ℝ), (5216138627/10000000000 : ℝ)] ![(94123705089/800000000000 : ℝ), (11029317145287/25000000000000 : ℝ), (44117268272749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113949961/625000000 : ℝ)|^5003 ≤ (94123705089/800000000000 : ℝ)^3979
        have hw : |(-113949961/625000000 : ℝ)|=(113949961/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163004333/312500000 : ℝ)|^5003 ≤ (11029317145287/25000000000000 : ℝ)^3979
        have hw : |(163004333/312500000 : ℝ)|=(163004333/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216138627/10000000000 : ℝ)|^5003 ≤ (44117268272749/100000000000000 : ℝ)^3979
        have hw : |(5216138627/10000000000 : ℝ)|=(5216138627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_5 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689265043/5000000000 : ℝ)*x 0 + (-100380329/625000000 : ℝ)*x 1 + (5216138831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689265043/5000000000 : ℝ)^5003 ≤ (45851081706929/100000000000000 : ℝ)^3979 := by
    have hnat : (2689265043 : ℕ)^5003*100000000000000^3979 ≤ 45851081706929^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689265043 5000000000 45851081706929 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100380329/625000000 : ℝ)^5003 ≤ (2507911958791/25000000000000 : ℝ)^3979 := by
    have hnat : (100380329 : ℕ)^5003*25000000000000^3979 ≤ 2507911958791^3979*625000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100380329 625000000 2507911958791 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216138831/10000000000 : ℝ)^5003 ≤ (44117270442181/100000000000000 : ℝ)^3979 := by
    have hnat : (5216138831 : ℕ)^5003*100000000000000^3979 ≤ 44117270442181^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216138831 10000000000 44117270442181 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689265043/5000000000 : ℝ), (-100380329/625000000 : ℝ), (5216138831/10000000000 : ℝ)] ![(45851081706929/100000000000000 : ℝ), (2507911958791/25000000000000 : ℝ), (44117270442181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689265043/5000000000 : ℝ)|^5003 ≤ (45851081706929/100000000000000 : ℝ)^3979
        have hw : |(2689265043/5000000000 : ℝ)|=(2689265043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100380329/625000000 : ℝ)|^5003 ≤ (2507911958791/25000000000000 : ℝ)^3979
        have hw : |(-100380329/625000000 : ℝ)|=(100380329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216138831/10000000000 : ℝ)|^5003 ≤ (44117270442181/100000000000000 : ℝ)^3979
        have hw : |(5216138831/10000000000 : ℝ)|=(5216138831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_6 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689265177/5000000000 : ℝ)*x 0 + (5216138439/10000000000 : ℝ)*x 1 + (-1606085429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689265177/5000000000 : ℝ)^5003 ≤ (45851084579543/100000000000000 : ℝ)^3979 := by
    have hnat : (2689265177 : ℕ)^5003*100000000000000^3979 ≤ 45851084579543^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689265177 5000000000 45851084579543 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216138439/10000000000 : ℝ)^5003 ≤ (44117266273467/100000000000000 : ℝ)^3979 := by
    have hnat : (5216138439 : ℕ)^5003*100000000000000^3979 ≤ 44117266273467^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216138439 10000000000 44117266273467 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1606085429/10000000000 : ℝ)^5003 ≤ (5015824565491/50000000000000 : ℝ)^3979 := by
    have hnat : (1606085429 : ℕ)^5003*50000000000000^3979 ≤ 5015824565491^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606085429 10000000000 5015824565491 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689265177/5000000000 : ℝ), (5216138439/10000000000 : ℝ), (-1606085429/10000000000 : ℝ)] ![(45851084579543/100000000000000 : ℝ), (44117266273467/100000000000000 : ℝ), (5015824565491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689265177/5000000000 : ℝ)|^5003 ≤ (45851084579543/100000000000000 : ℝ)^3979
        have hw : |(2689265177/5000000000 : ℝ)|=(2689265177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216138439/10000000000 : ℝ)|^5003 ≤ (44117266273467/100000000000000 : ℝ)^3979
        have hw : |(5216138439/10000000000 : ℝ)|=(5216138439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1606085429/10000000000 : ℝ)|^5003 ≤ (5015824565491/50000000000000 : ℝ)^3979
        have hw : |(-1606085429/10000000000 : ℝ)|=(1606085429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_7 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1941304531/5000000000 : ℝ)*x 0 + (4317476633/10000000000 : ℝ)*x 1 + (863495313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941304531/5000000000 : ℝ)^5003 ≤ (243486101711/800000000000 : ℝ)^3979 := by
    have hnat : (1941304531 : ℕ)^5003*800000000000^3979 ≤ 243486101711^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941304531 5000000000 243486101711 800000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317476633/10000000000 : ℝ)^5003 ≤ (1739105949129/5000000000000 : ℝ)^3979 := by
    have hnat : (4317476633 : ℕ)^5003*5000000000000^3979 ≤ 1739105949129^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317476633 10000000000 1739105949129 5000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863495313/2000000000 : ℝ)^5003 ≤ (34782118293783/100000000000000 : ℝ)^3979 := by
    have hnat : (863495313 : ℕ)^5003*100000000000000^3979 ≤ 34782118293783^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863495313 2000000000 34782118293783 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1941304531/5000000000 : ℝ), (4317476633/10000000000 : ℝ), (863495313/2000000000 : ℝ)] ![(243486101711/800000000000 : ℝ), (1739105949129/5000000000000 : ℝ), (34782118293783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1941304531/5000000000 : ℝ)|^5003 ≤ (243486101711/800000000000 : ℝ)^3979
        have hw : |(1941304531/5000000000 : ℝ)|=(1941304531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317476633/10000000000 : ℝ)|^5003 ≤ (1739105949129/5000000000000 : ℝ)^3979
        have hw : |(4317476633/10000000000 : ℝ)|=(4317476633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863495313/2000000000 : ℝ)|^5003 ≤ (34782118293783/100000000000000 : ℝ)^3979
        have hw : |(863495313/2000000000 : ℝ)|=(863495313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_8 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-428464699/2500000000 : ℝ)*x 0 + (5081315127/10000000000 : ℝ)*x 1 + (169754467/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428464699/2500000000 : ℝ)^5003 ≤ (10885231662839/100000000000000 : ℝ)^3979 := by
    have hnat : (428464699 : ℕ)^5003*100000000000000^3979 ≤ 10885231662839^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428464699 2500000000 10885231662839 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081315127/10000000000 : ℝ)^5003 ≤ (21344145318767/50000000000000 : ℝ)^3979 := by
    have hnat : (5081315127 : ℕ)^5003*50000000000000^3979 ≤ 21344145318767^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081315127 10000000000 21344145318767 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169754467/312500000 : ℝ)^5003 ≤ (46426477685031/100000000000000 : ℝ)^3979 := by
    have hnat : (169754467 : ℕ)^5003*100000000000000^3979 ≤ 46426477685031^3979*312500000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169754467 312500000 46426477685031 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428464699/2500000000 : ℝ), (5081315127/10000000000 : ℝ), (169754467/312500000 : ℝ)] ![(10885231662839/100000000000000 : ℝ), (21344145318767/50000000000000 : ℝ), (46426477685031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428464699/2500000000 : ℝ)|^5003 ≤ (10885231662839/100000000000000 : ℝ)^3979
        have hw : |(-428464699/2500000000 : ℝ)|=(428464699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081315127/10000000000 : ℝ)|^5003 ≤ (21344145318767/50000000000000 : ℝ)^3979
        have hw : |(5081315127/10000000000 : ℝ)|=(5081315127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169754467/312500000 : ℝ)|^5003 ≤ (46426477685031/100000000000000 : ℝ)^3979
        have hw : |(169754467/312500000 : ℝ)|=(169754467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_9 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307671263/2500000000 : ℝ)*x 0 + (-1512400461/10000000000 : ℝ)*x 1 + (5432143077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307671263/2500000000 : ℝ)^5003 ≤ (8854403467419/20000000000000 : ℝ)^3979 := by
    have hnat : (1307671263 : ℕ)^5003*20000000000000^3979 ≤ 8854403467419^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307671263 2500000000 8854403467419 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512400461/10000000000 : ℝ)^5003 ≤ (1162687942007/12500000000000 : ℝ)^3979 := by
    have hnat : (1512400461 : ℕ)^5003*12500000000000^3979 ≤ 1162687942007^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512400461 10000000000 1162687942007 12500000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432143077/10000000000 : ℝ)^5003 ≤ (46426479114263/100000000000000 : ℝ)^3979 := by
    have hnat : (5432143077 : ℕ)^5003*100000000000000^3979 ≤ 46426479114263^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432143077 10000000000 46426479114263 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307671263/2500000000 : ℝ), (-1512400461/10000000000 : ℝ), (5432143077/10000000000 : ℝ)] ![(8854403467419/20000000000000 : ℝ), (1162687942007/12500000000000 : ℝ), (46426479114263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307671263/2500000000 : ℝ)|^5003 ≤ (8854403467419/20000000000000 : ℝ)^3979
        have hw : |(1307671263/2500000000 : ℝ)|=(1307671263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512400461/10000000000 : ℝ)|^5003 ≤ (1162687942007/12500000000000 : ℝ)^3979
        have hw : |(-1512400461/10000000000 : ℝ)|=(1512400461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432143077/10000000000 : ℝ)|^5003 ≤ (46426479114263/100000000000000 : ℝ)^3979
        have hw : |(5432143077/10000000000 : ℝ)|=(5432143077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_10 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307671277/2500000000 : ℝ)*x 0 + (1086428613/2000000000 : ℝ)*x 1 + (-1512400399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307671277/2500000000 : ℝ)^5003 ≤ (11068004483263/25000000000000 : ℝ)^3979 := by
    have hnat : (1307671277 : ℕ)^5003*25000000000000^3979 ≤ 11068004483263^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307671277 2500000000 11068004483263 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086428613/2000000000 : ℝ)^5003 ≤ (4642647898531/10000000000000 : ℝ)^3979 := by
    have hnat : (1086428613 : ℕ)^5003*10000000000000^3979 ≤ 4642647898531^3979*2000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086428613 2000000000 4642647898531 10000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512400399/10000000000 : ℝ)^5003 ≤ (1860300611323/20000000000000 : ℝ)^3979 := by
    have hnat : (1512400399 : ℕ)^5003*20000000000000^3979 ≤ 1860300611323^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512400399 10000000000 1860300611323 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307671277/2500000000 : ℝ), (1086428613/2000000000 : ℝ), (-1512400399/10000000000 : ℝ)] ![(11068004483263/25000000000000 : ℝ), (4642647898531/10000000000000 : ℝ), (1860300611323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307671277/2500000000 : ℝ)|^5003 ≤ (11068004483263/25000000000000 : ℝ)^3979
        have hw : |(1307671277/2500000000 : ℝ)|=(1307671277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086428613/2000000000 : ℝ)|^5003 ≤ (4642647898531/10000000000000 : ℝ)^3979
        have hw : |(1086428613/2000000000 : ℝ)|=(1086428613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1512400399/10000000000 : ℝ)|^5003 ≤ (1860300611323/20000000000000 : ℝ)^3979
        have hw : |(-1512400399/10000000000 : ℝ)|=(1512400399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_11 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (181009731/400000000 : ℝ)*x 0 + (49940777/125000000 : ℝ)*x 1 + (1997630883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181009731/400000000 : ℝ)^5003 ≤ (1153110768713/3125000000000 : ℝ)^3979 := by
    have hnat : (181009731 : ℕ)^5003*3125000000000^3979 ≤ 1153110768713^3979*400000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181009731 400000000 1153110768713 3125000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49940777/125000000 : ℝ)^5003 ≤ (6310045929289/20000000000000 : ℝ)^3979 := by
    have hnat : (49940777 : ℕ)^5003*20000000000000^3979 ≤ 6310045929289^3979*125000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49940777 125000000 6310045929289 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997630883/5000000000 : ℝ)^5003 ≤ (6310045146869/20000000000000 : ℝ)^3979 := by
    have hnat : (1997630883 : ℕ)^5003*20000000000000^3979 ≤ 6310045146869^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997630883 5000000000 6310045146869 20000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181009731/400000000 : ℝ), (49940777/125000000 : ℝ), (1997630883/5000000000 : ℝ)] ![(1153110768713/3125000000000 : ℝ), (6310045929289/20000000000000 : ℝ), (6310045146869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181009731/400000000 : ℝ)|^5003 ≤ (1153110768713/3125000000000 : ℝ)^3979
        have hw : |(181009731/400000000 : ℝ)|=(181009731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49940777/125000000 : ℝ)|^5003 ≤ (6310045929289/20000000000000 : ℝ)^3979
        have hw : |(49940777/125000000 : ℝ)|=(49940777/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1997630883/5000000000 : ℝ)|^5003 ≤ (6310045146869/20000000000000 : ℝ)^3979
        have hw : |(1997630883/5000000000 : ℝ)|=(1997630883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_12 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1418650179/10000000000 : ℝ)*x 0 + (2766385251/5000000000 : ℝ)*x 1 + (2598187133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1418650179/10000000000 : ℝ)^5003 ≤ (8582414841677/100000000000000 : ℝ)^3979 := by
    have hnat : (1418650179 : ℕ)^5003*100000000000000^3979 ≤ 8582414841677^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418650179 10000000000 8582414841677 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2766385251/5000000000 : ℝ)^5003 ≤ (23755198952097/50000000000000 : ℝ)^3979 := by
    have hnat : (2766385251 : ℕ)^5003*50000000000000^3979 ≤ 23755198952097^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766385251 5000000000 23755198952097 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598187133/5000000000 : ℝ)^5003 ≤ (21953593622419/50000000000000 : ℝ)^3979 := by
    have hnat : (2598187133 : ℕ)^5003*50000000000000^3979 ≤ 21953593622419^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598187133 5000000000 21953593622419 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1418650179/10000000000 : ℝ), (2766385251/5000000000 : ℝ), (2598187133/5000000000 : ℝ)] ![(8582414841677/100000000000000 : ℝ), (23755198952097/50000000000000 : ℝ), (21953593622419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1418650179/10000000000 : ℝ)|^5003 ≤ (8582414841677/100000000000000 : ℝ)^3979
        have hw : |(-1418650179/10000000000 : ℝ)|=(1418650179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2766385251/5000000000 : ℝ)|^5003 ≤ (23755198952097/50000000000000 : ℝ)^3979
        have hw : |(2766385251/5000000000 : ℝ)|=(2766385251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598187133/5000000000 : ℝ)|^5003 ≤ (21953593622419/50000000000000 : ℝ)^3979
        have hw : |(2598187133/5000000000 : ℝ)|=(2598187133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_13 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392069443/10000000000 : ℝ)*x 0 + (-1614344861/10000000000 : ℝ)*x 1 + (5196374511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392069443/10000000000 : ℝ)^5003 ≤ (919925062713/2000000000000 : ℝ)^3979 := by
    have hnat : (5392069443 : ℕ)^5003*2000000000000^3979 ≤ 919925062713^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392069443 10000000000 919925062713 2000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614344861/10000000000 : ℝ)^5003 ≤ (5048278500751/50000000000000 : ℝ)^3979 := by
    have hnat : (1614344861 : ℕ)^5003*50000000000000^3979 ≤ 5048278500751^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614344861 10000000000 5048278500751 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196374511/10000000000 : ℝ)^5003 ≤ (2195359492387/5000000000000 : ℝ)^3979 := by
    have hnat : (5196374511 : ℕ)^5003*5000000000000^3979 ≤ 2195359492387^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196374511 10000000000 2195359492387 5000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392069443/10000000000 : ℝ), (-1614344861/10000000000 : ℝ), (5196374511/10000000000 : ℝ)] ![(919925062713/2000000000000 : ℝ), (5048278500751/50000000000000 : ℝ), (2195359492387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392069443/10000000000 : ℝ)|^5003 ≤ (919925062713/2000000000000 : ℝ)^3979
        have hw : |(5392069443/10000000000 : ℝ)|=(5392069443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1614344861/10000000000 : ℝ)|^5003 ≤ (5048278500751/50000000000000 : ℝ)^3979
        have hw : |(-1614344861/10000000000 : ℝ)|=(1614344861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196374511/10000000000 : ℝ)|^5003 ≤ (2195359492387/5000000000000 : ℝ)^3979
        have hw : |(5196374511/10000000000 : ℝ)|=(5196374511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_14 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392069409/10000000000 : ℝ)*x 0 + (519637469/1000000000 : ℝ)*x 1 + (-807172333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392069409/10000000000 : ℝ)^5003 ≤ (22998126385489/50000000000000 : ℝ)^3979 := by
    have hnat : (5392069409 : ℕ)^5003*50000000000000^3979 ≤ 22998126385489^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392069409 10000000000 22998126385489 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519637469/1000000000 : ℝ)^5003 ≤ (10976797937363/25000000000000 : ℝ)^3979 := by
    have hnat : (519637469 : ℕ)^5003*25000000000000^3979 ≤ 10976797937363^3979*1000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519637469 1000000000 10976797937363 25000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807172333/5000000000 : ℝ)^5003 ≤ (5048277734029/50000000000000 : ℝ)^3979 := by
    have hnat : (807172333 : ℕ)^5003*50000000000000^3979 ≤ 5048277734029^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807172333 5000000000 5048277734029 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392069409/10000000000 : ℝ), (519637469/1000000000 : ℝ), (-807172333/5000000000 : ℝ)] ![(22998126385489/50000000000000 : ℝ), (10976797937363/25000000000000 : ℝ), (5048277734029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392069409/10000000000 : ℝ)|^5003 ≤ (22998126385489/50000000000000 : ℝ)^3979
        have hw : |(5392069409/10000000000 : ℝ)|=(5392069409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519637469/1000000000 : ℝ)|^5003 ≤ (10976797937363/25000000000000 : ℝ)^3979
        have hw : |(519637469/1000000000 : ℝ)|=(519637469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-807172333/5000000000 : ℝ)|^5003 ≤ (5048277734029/50000000000000 : ℝ)^3979
        have hw : |(-807172333/5000000000 : ℝ)|=(807172333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1671_box_15 (p : ℝ) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1910981627/5000000000 : ℝ)*x 0 + (1086724281/2500000000 : ℝ)*x 1 + (4346896811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910981627/5000000000 : ℝ)^5003 ≤ (14919610576211/50000000000000 : ℝ)^3979 := by
    have hnat : (1910981627 : ℕ)^5003*50000000000000^3979 ≤ 14919610576211^3979*5000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910981627 5000000000 14919610576211 50000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086724281/2500000000 : ℝ)^5003 ≤ (35080391003619/100000000000000 : ℝ)^3979 := by
    have hnat : (1086724281 : ℕ)^5003*100000000000000^3979 ≤ 35080391003619^3979*2500000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086724281 2500000000 35080391003619 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4346896811/10000000000 : ℝ)^5003 ≤ (35080387827579/100000000000000 : ℝ)^3979 := by
    have hnat : (4346896811 : ℕ)^5003*100000000000000^3979 ≤ 35080387827579^3979*10000000000^5003 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346896811 10000000000 35080387827579 100000000000000 5003 3979 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5003/1024 : ℝ)) 5003 3979 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1910981627/5000000000 : ℝ), (1086724281/2500000000 : ℝ), (4346896811/10000000000 : ℝ)] ![(14919610576211/50000000000000 : ℝ), (35080391003619/100000000000000 : ℝ), (35080387827579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1910981627/5000000000 : ℝ)|^5003 ≤ (14919610576211/50000000000000 : ℝ)^3979
        have hw : |(1910981627/5000000000 : ℝ)|=(1910981627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086724281/2500000000 : ℝ)|^5003 ≤ (35080391003619/100000000000000 : ℝ)^3979
        have hw : |(1086724281/2500000000 : ℝ)|=(1086724281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4346896811/10000000000 : ℝ)|^5003 ≤ (35080387827579/100000000000000 : ℝ)^3979
        have hw : |(4346896811/10000000000 : ℝ)|=(4346896811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1671_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (649/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1629/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14713/25000 : ℝ) ∧ (8157/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11053/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (649/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (649/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (649/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (649/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (649/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (649/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5387/50000 : ℝ) ^ (4999/1024 : ℝ) ≤ (944480788473839/50000000000000000000 : ℝ) := by
    have hpowers : (5387/50000 : ℝ)^4999 ≤ (944480788473839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5387 : ℕ)^4999*50000000000000000000^1024 ≤ 944480788473839^1024*50000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5387 50000 944480788473839 50000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5387/50000 : ℝ)) (X := (944480788473839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (649/4000 : ℝ) ^ (4999/1024 : ℝ) ≤ (13939632078742103/100000000000000000000 : ℝ) := by
    have hpowers : (649/4000 : ℝ)^4999 ≤ (13939632078742103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (649 : ℕ)^4999*100000000000000000000^1024 ≤ 13939632078742103^1024*4000^4999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        649 4000 13939632078742103 100000000000000000000 4999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (649/4000 : ℝ)) (X := (13939632078742103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000944480788473839/25000000000000000000 : ℝ) ≤ (1000007738618131/1000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (25000944480788473839/25000000000000000000 : ℝ)^1024 ≤ (1000007738618131/1000000000000000 : ℝ)^4999 := by
      have hnat : (25000944480788473839 : ℕ)^1024*1000000000000000^4999 ≤ 1000007738618131^4999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000944480788473839 25000000000000000000 1000007738618131 1000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000007738618131/1000000000000000 : ℝ)) (X := (25000944480788473839/25000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015828593655689781/100000000000000000000 : ℝ) ≤ (10000324214042413/10000000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (100015828593655689781/100000000000000000000 : ℝ)^1024 ≤ (10000324214042413/10000000000000000 : ℝ)^4999 := by
      have hnat : (100015828593655689781 : ℕ)^1024*10000000000000000^4999 ≤ 10000324214042413^4999*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015828593655689781 100000000000000000000 10000324214042413 10000000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000324214042413/10000000000000000 : ℝ)) (X := (100015828593655689781/100000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013939632078742103/50000000000000000000 : ℝ) ≤ (2500142760475879/2500000000000000 : ℝ) ^ (4999/1024 : ℝ) := by
    have hpowers : (50013939632078742103/50000000000000000000 : ℝ)^1024 ≤ (2500142760475879/2500000000000000 : ℝ)^4999 := by
      have hnat : (50013939632078742103 : ℕ)^1024*2500000000000000^4999 ≤ 2500142760475879^4999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013939632078742103 50000000000000000000 2500142760475879 2500000000000000 1024 4999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500142760475879/2500000000000000 : ℝ)) (X := (50013939632078742103/50000000000000000000 : ℝ)) (by norm_num) 4999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(944480788473839/50000000000000000000 : ℝ) ≤ ((9084183864220545561/9085000000000000000 : ℝ)+2*(82275953701/181700000000000 : ℝ)*(5387/50000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (9084183864220545561/9085000000000000000 : ℝ)+2*(82275953701/181700000000000 : ℝ)*(5387/50000 : ℝ)=(1000007738618131/1000000000000000 : ℝ) by norm_num, show 1+2*(944480788473839/50000000000000000000 : ℝ)=(25000944480788473839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13939632078742103/100000000000000000000 : ℝ)+(944480788473839/50000000000000000000 : ℝ) ≤ ((9084183864220545561/9085000000000000000 : ℝ)+(82275953701/181700000000000 : ℝ)*((649/4000 : ℝ)+(5387/50000 : ℝ)))^(4999/1024 : ℝ) := by
    rw [show (9084183864220545561/9085000000000000000 : ℝ)+(82275953701/181700000000000 : ℝ)*((649/4000 : ℝ)+(5387/50000 : ℝ))=(10000324214042413/10000000000000000 : ℝ) by norm_num, show 1+(13939632078742103/100000000000000000000 : ℝ)+(944480788473839/50000000000000000000 : ℝ)=(100015828593655689781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13939632078742103/100000000000000000000 : ℝ) ≤ ((9084183864220545561/9085000000000000000 : ℝ)+2*(82275953701/181700000000000 : ℝ)*(649/4000 : ℝ))^(4999/1024 : ℝ) := by
    rw [show (9084183864220545561/9085000000000000000 : ℝ)+2*(82275953701/181700000000000 : ℝ)*(649/4000 : ℝ)=(2500142760475879/2500000000000000 : ℝ) by norm_num, show 1+2*(13939632078742103/100000000000000000000 : ℝ)=(50013939632078742103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9084183864220545561/9085000000000000000 : ℝ)*(X 1 0+X 2 0)+(82275953701/181700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (649/4000 : ℝ)) (c := (9084183864220545561/9085000000000000000 : ℝ)) (alpha := (82275953701/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9084183864220545561/9085000000000000000 : ℝ)*(X 0 1+X 2 1)+(82275953701/181700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (649/4000 : ℝ)) (c := (9084183864220545561/9085000000000000000 : ℝ)) (alpha := (82275953701/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9084183864220545561/9085000000000000000 : ℝ)*(X 0 2+X 1 2)+(82275953701/181700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4999/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (649/4000 : ℝ)) (c := (9084183864220545561/9085000000000000000 : ℝ)) (alpha := (82275953701/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1311315399/10000000000 : ℝ)*X 0 0+(1350737097/2500000000 : ℝ)*X 0 1+(5402948507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625332181/5000000000 : ℝ)*X 1 0+(-381354889/2500000000 : ℝ)*X 1 1+(1080589659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((328166509/625000000 : ℝ)*X 2 0+(1350737119/2500000000 : ℝ)*X 2 1+(-305083921/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((444043407/1000000000 : ℝ)*X 0 0+(1009720221/2500000000 : ℝ)*X 0 1+(2019440279/5000000000 : ℝ)*X 0 2+(444043407/1000000000 : ℝ)*X 1 0+(1009720221/2500000000 : ℝ)*X 1 1+(2019440279/5000000000 : ℝ)*X 1 2+(444043407/1000000000 : ℝ)*X 2 0+(1009720221/2500000000 : ℝ)*X 2 1+(2019440279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-113949961/625000000 : ℝ)*X 0 0+(163004333/312500000 : ℝ)*X 0 1+(5216138627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2689265043/5000000000 : ℝ)*X 1 0+(-100380329/625000000 : ℝ)*X 1 1+(5216138831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2689265177/5000000000 : ℝ)*X 2 0+(5216138439/10000000000 : ℝ)*X 2 1+(-1606085429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1941304531/5000000000 : ℝ)*X 0 0+(4317476633/10000000000 : ℝ)*X 0 1+(863495313/2000000000 : ℝ)*X 0 2+(1941304531/5000000000 : ℝ)*X 1 0+(4317476633/10000000000 : ℝ)*X 1 1+(863495313/2000000000 : ℝ)*X 1 2+(1941304531/5000000000 : ℝ)*X 2 0+(4317476633/10000000000 : ℝ)*X 2 1+(863495313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-428464699/2500000000 : ℝ)*X 0 0+(5081315127/10000000000 : ℝ)*X 0 1+(169754467/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307671263/2500000000 : ℝ)*X 1 0+(-1512400461/10000000000 : ℝ)*X 1 1+(5432143077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307671277/2500000000 : ℝ)*X 2 0+(1086428613/2000000000 : ℝ)*X 2 1+(-1512400399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((181009731/400000000 : ℝ)*X 0 0+(49940777/125000000 : ℝ)*X 0 1+(1997630883/5000000000 : ℝ)*X 0 2+(181009731/400000000 : ℝ)*X 1 0+(49940777/125000000 : ℝ)*X 1 1+(1997630883/5000000000 : ℝ)*X 1 2+(181009731/400000000 : ℝ)*X 2 0+(49940777/125000000 : ℝ)*X 2 1+(1997630883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1418650179/10000000000 : ℝ)*X 0 0+(2766385251/5000000000 : ℝ)*X 0 1+(2598187133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392069443/10000000000 : ℝ)*X 1 0+(-1614344861/10000000000 : ℝ)*X 1 1+(5196374511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392069409/10000000000 : ℝ)*X 2 0+(519637469/1000000000 : ℝ)*X 2 1+(-807172333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1910981627/5000000000 : ℝ)*X 0 0+(1086724281/2500000000 : ℝ)*X 0 1+(4346896811/10000000000 : ℝ)*X 0 2+(1910981627/5000000000 : ℝ)*X 1 0+(1086724281/2500000000 : ℝ)*X 1 1+(4346896811/10000000000 : ℝ)*X 1 2+(1910981627/5000000000 : ℝ)*X 2 0+(1086724281/2500000000 : ℝ)*X 2 1+(4346896811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1671_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1629/2500 : ℝ) ≤ (-147987971650144620677950836069027/227125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (667791/10000000000000 : ℝ)*(upper1) + (15251751/50000000000000 : ℝ)*(upper3) + (15634897/50000000000000 : ℝ)*(upper5) + (899318521132877/50000000000000 : ℝ)*(major0) + (899318521132877/50000000000000 : ℝ)*(major1) + (899318521132877/50000000000000 : ℝ)*(major2) + (138173671/3125000000000 : ℝ)*(sp2) + (1140031163/100000000000000 : ℝ)*(sp3) + (52700138471083/2000000000000 : ℝ)*(sp4) + (658749239279861/25000000000000 : ℝ)*(sp5) + (21080023487369/800000000000 : ℝ)*(sp6) + (983984606893339/100000000000000 : ℝ)*(sp7) + (13560139/3125000000000 : ℝ)*(sp8) + (5200179577/50000000000000 : ℝ)*(sp13) + (983985746924501/100000000000000 : ℝ)*(f.failure) + (2635007357478597/100000000000000 : ℝ)*(f.sum) + (1904753485073/4542500000000000000000000000 : ℝ)*base66 + (2756195851291391003/454250000000000000000000000000000 : ℝ)*base68 + (8371994787764391003/454250000000000000000000000000000 : ℝ)*base70 + (4623845570742141003/454250000000000000000000000000000 : ℝ)*base72 + (25071267870689/9085000000000000000000000000 : ℝ)*base73 + (8586040429422391003/454250000000000000000000000000000 : ℝ)*base76 + (2202551713593141003/454250000000000000000000000000000 : ℝ)*base78 + (2098300693558141003/454250000000000000000000000000000 : ℝ)*base80 + (36098724169357/4542500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (16013307/2000000000000000000000 : ℝ)*base90 + (16013307/2000000000000000000000 : ℝ)*base92 + (16013307/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14713/25000 : ℝ) ≤ (1692061112481613705872922150203/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37970341/100000000000000 : ℝ)*(lower0) + (17957027/100000000000000 : ℝ)*(upper1) + (5747379/12500000000000 : ℝ)*(upper2) + (946008109630387/50000000000000 : ℝ)*(major0) + (946008109630387/50000000000000 : ℝ)*(major1) + (946008109630387/50000000000000 : ℝ)*(major2) + (109173727274959/4000000000000 : ℝ)*(sp0) + (341166375095159/12500000000000 : ℝ)*(sp1) + (2729337768011861/100000000000000 : ℝ)*(sp2) + (1035070415375347/100000000000000 : ℝ)*(sp3) + (278615157/50000000000000 : ℝ)*(sp7) + (12365299749/100000000000000 : ℝ)*(sp9) + (139951229/2500000000000 : ℝ)*(sp10) + (92093523/50000000000000 : ℝ)*(sp12) + (1035070972605661/100000000000000 : ℝ)*(f.failure) + (2729343366061021/100000000000000 : ℝ)*(f.sum) + (462159325521/115000000000000000000000000 : ℝ)*base65 + (14414234058030533/5750000000000000000000000000000 : ℝ)*base67 + (38767670811780533/5750000000000000000000000000000 : ℝ)*base69 + (33435353267030533/5750000000000000000000000000000 : ℝ)*base71 + (456611209171/115000000000000000000000000 : ℝ)*base73 + (3340452537780533/5750000000000000000000000000000 : ℝ)*base75 + (48215838368030533/5750000000000000000000000000000 : ℝ)*base77 + (20404412455030533/5750000000000000000000000000000 : ℝ)*base79 + (99465000559/115000000000000000000000000 : ℝ)*base82 + (12269427/2000000000000000000000 : ℝ)*base90 + (12269427/2000000000000000000000 : ℝ)*base92 + (12269427/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8157/10000 : ℝ) ≤ (18527170611672298770550278496521/22712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8007257/100000000000000 : ℝ)*(lower3) + (22282547/50000000000000 : ℝ)*(upper4) + (51664149/100000000000000 : ℝ)*(lower5) + (99027541022571/5000000000000 : ℝ)*(major0) + (99027541022571/5000000000000 : ℝ)*(major1) + (99027541022571/5000000000000 : ℝ)*(major2) + (1882119093/50000000000000 : ℝ)*(sp0) + (19492224541/100000000000000 : ℝ)*(sp1) + (33808911583/100000000000000 : ℝ)*(sp2) + (9913946841/50000000000000 : ℝ)*(sp3) + (178150072333333/6250000000000 : ℝ)*(sp8) + (1425192714673487/50000000000000 : ℝ)*(sp9) + (712592778164983/25000000000000 : ℝ)*(sp10) + (1083486033816397/100000000000000 : ℝ)*(sp11) + (846488954461/78125000000 : ℝ)*(f.failure) + (1425202460785757/50000000000000 : ℝ)*(f.sum) + (2458652545263/1817000000000000000000000000 : ℝ)*base65 + (176487197334807331/45425000000000000000000000000000 : ℝ)*base67 + (78517811581807331/45425000000000000000000000000000 : ℝ)*base69 + (190966090251282331/45425000000000000000000000000000 : ℝ)*base71 + (1004393496759/908500000000000000000000000 : ℝ)*base73 + (150935225146732331/45425000000000000000000000000000 : ℝ)*base75 + (165921828791132331/45425000000000000000000000000000 : ℝ)*base77 + (164614362242607331/45425000000000000000000000000000 : ℝ)*base79 + (2435922933191/1817000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11473/1562500000000000000 : ℝ)*base89 + (11473/1562500000000000000 : ℝ)*base91 + (11473/1562500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-11053/12500 : ℝ) ≤ (-100414063372981668513260399236917/113562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15249051/50000000000000 : ℝ)*(lower0) + (19549567/100000000000000 : ℝ)*(lower1) + (42657003/50000000000000 : ℝ)*(lower2) + (39312297/100000000000000 : ℝ)*(lower4) + (1012857682910801/50000000000000 : ℝ)*(major0) + (1012857682910801/50000000000000 : ℝ)*(major1) + (1012857682910801/50000000000000 : ℝ)*(major2) + (273146957/4000000000000 : ℝ)*(sp0) + (44414106977/100000000000000 : ℝ)*(sp5) + (185804517/6250000000000 : ℝ)*(sp6) + (1486341844157167/50000000000000 : ℝ)*(sp12) + (2972646102881283/100000000000000 : ℝ)*(sp13) + (743171886028997/25000000000000 : ℝ)*(sp14) + (554107082322587/50000000000000 : ℝ)*(sp15) + (554107082322587/50000000000000 : ℝ)*(f.failure) + (148634525849413/5000000000000 : ℝ)*(f.sum) + (71327344309473/9085000000000000000000000000 : ℝ)*base66 + (489535498967445639/454250000000000000000000000000000 : ℝ)*base68 + (119518000129304361/454250000000000000000000000000000 : ℝ)*base69 + (2567340157950195639/454250000000000000000000000000000 : ℝ)*base72 + (27000326974723/9085000000000000000000000000 : ℝ)*base74 + (594923075214945639/454250000000000000000000000000000 : ℝ)*base76 + (3213106495453445639/454250000000000000000000000000000 : ℝ)*base78 + (3291644107347445639/454250000000000000000000000000000 : ℝ)*base80 + (2465450027941/1135625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3805291/1000000000000000000000 : ℝ)*base89 + (3805291/1000000000000000000000 : ℝ)*base91 + (3805291/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1671_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (649/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1629/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(14713/25000 : ℝ) else (8157/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11053/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1671_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1671_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (407/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1629/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(14713/25000 : ℝ) else (8157/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11053/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1671_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1671_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1671_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4999/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36558193/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (407/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1629/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(14713/25000 : ℝ) else (8157/10000 : ℝ) ≤ X j i ∧ X j i ≤ (11053/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1671_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
