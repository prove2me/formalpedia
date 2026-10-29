-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:52.959993+00:00
-- url     : https://prove2.me/submissions/5ea7e6cf-69dc-4672-bd3e-123302321fad

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
theorem support_rectangle_w1758_s3_0 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1178986097/10000000000 : ℝ)*x 0 + (1371610423/2500000000 : ℝ)*x 1 + (1016653301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178986097/10000000000 : ℝ)^5903 ≤ (7527275064971/100000000000000 : ℝ)^4879 := by
    have hnat : (1178986097 : ℕ)^5903*100000000000000^4879 ≤ 7527275064971^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178986097 10000000000 7527275064971 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371610423/2500000000 : ℝ)^5903 ≤ (24184847892029/50000000000000 : ℝ)^4879 := by
    have hnat : (1371610423 : ℕ)^5903*50000000000000^4879 ≤ 24184847892029^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371610423 2500000000 24184847892029 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016653301/2000000000 : ℝ)^5903 ≤ (11025757284161/25000000000000 : ℝ)^4879 := by
    have hnat : (1016653301 : ℕ)^5903*25000000000000^4879 ≤ 11025757284161^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016653301 2000000000 11025757284161 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1178986097/10000000000 : ℝ), (1371610423/2500000000 : ℝ), (1016653301/2000000000 : ℝ)] ![(7527275064971/100000000000000 : ℝ), (24184847892029/50000000000000 : ℝ), (11025757284161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1178986097/10000000000 : ℝ)|^5903 ≤ (7527275064971/100000000000000 : ℝ)^4879
        have hw : |(-1178986097/10000000000 : ℝ)|=(1178986097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371610423/2500000000 : ℝ)|^5903 ≤ (24184847892029/50000000000000 : ℝ)^4879
        have hw : |(1371610423/2500000000 : ℝ)|=(1371610423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016653301/2000000000 : ℝ)|^5903 ≤ (11025757284161/25000000000000 : ℝ)^4879
        have hw : |(1016653301/2000000000 : ℝ)|=(1016653301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_1 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2665357449/5000000000 : ℝ)*x 0 + (-1389603419/10000000000 : ℝ)*x 1 + (1016653299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2665357449/5000000000 : ℝ)^5903 ≤ (1868544442169/4000000000000 : ℝ)^4879 := by
    have hnat : (2665357449 : ℕ)^5903*4000000000000^4879 ≤ 1868544442169^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665357449 5000000000 1868544442169 4000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389603419/10000000000 : ℝ)^5903 ≤ (229583997401/2500000000000 : ℝ)^4879 := by
    have hnat : (1389603419 : ℕ)^5903*2500000000000^4879 ≤ 229583997401^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389603419 10000000000 229583997401 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016653299/2000000000 : ℝ)^5903 ≤ (44103029031673/100000000000000 : ℝ)^4879 := by
    have hnat : (1016653299 : ℕ)^5903*100000000000000^4879 ≤ 44103029031673^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016653299 2000000000 44103029031673 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2665357449/5000000000 : ℝ), (-1389603419/10000000000 : ℝ), (1016653299/2000000000 : ℝ)] ![(1868544442169/4000000000000 : ℝ), (229583997401/2500000000000 : ℝ), (44103029031673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2665357449/5000000000 : ℝ)|^5903 ≤ (1868544442169/4000000000000 : ℝ)^4879
        have hw : |(2665357449/5000000000 : ℝ)|=(2665357449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389603419/10000000000 : ℝ)|^5903 ≤ (229583997401/2500000000000 : ℝ)^4879
        have hw : |(-1389603419/10000000000 : ℝ)|=(1389603419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016653299/2000000000 : ℝ)|^5903 ≤ (44103029031673/100000000000000 : ℝ)^4879
        have hw : |(1016653299/2000000000 : ℝ)|=(1016653299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_2 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106614299/200000000 : ℝ)*x 0 + (635408309/1250000000 : ℝ)*x 1 + (-1389603381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106614299/200000000 : ℝ)^5903 ≤ (9342722321109/20000000000000 : ℝ)^4879 := by
    have hnat : (106614299 : ℕ)^5903*20000000000000^4879 ≤ 9342722321109^4879*200000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106614299 200000000 9342722321109 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635408309/1250000000 : ℝ)^5903 ≤ (44103028790241/100000000000000 : ℝ)^4879 := by
    have hnat : (635408309 : ℕ)^5903*100000000000000^4879 ≤ 44103028790241^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635408309 1250000000 44103028790241 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389603381/10000000000 : ℝ)^5903 ≤ (4591679796103/50000000000000 : ℝ)^4879 := by
    have hnat : (1389603381 : ℕ)^5903*50000000000000^4879 ≤ 4591679796103^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389603381 10000000000 4591679796103 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106614299/200000000 : ℝ), (635408309/1250000000 : ℝ), (-1389603381/10000000000 : ℝ)] ![(9342722321109/20000000000000 : ℝ), (44103028790241/100000000000000 : ℝ), (4591679796103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106614299/200000000 : ℝ)|^5903 ≤ (9342722321109/20000000000000 : ℝ)^4879
        have hw : |(106614299/200000000 : ℝ)|=(106614299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635408309/1250000000 : ℝ)|^5903 ≤ (44103028790241/100000000000000 : ℝ)^4879
        have hw : |(635408309/1250000000 : ℝ)|=(635408309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389603381/10000000000 : ℝ)|^5903 ≤ (4591679796103/50000000000000 : ℝ)^4879
        have hw : |(-1389603381/10000000000 : ℝ)|=(1389603381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_3 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (400458811/1000000000 : ℝ)*x 0 + (26181509/78125000 : ℝ)*x 1 + (73737801/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400458811/1000000000 : ℝ)^5903 ≤ (16523919418569/50000000000000 : ℝ)^4879 := by
    have hnat : (400458811 : ℕ)^5903*50000000000000^4879 ≤ 16523919418569^4879*1000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400458811 1000000000 16523919418569 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26181509/78125000 : ℝ)^5903 ≤ (26641276754121/100000000000000 : ℝ)^4879 := by
    have hnat : (26181509 : ℕ)^5903*100000000000000^4879 ≤ 26641276754121^4879*78125000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26181509 78125000 26641276754121 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73737801/156250000 : ℝ)^5903 ≤ (40310884398289/100000000000000 : ℝ)^4879 := by
    have hnat : (73737801 : ℕ)^5903*100000000000000^4879 ≤ 40310884398289^4879*156250000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73737801 156250000 40310884398289 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(400458811/1000000000 : ℝ), (26181509/78125000 : ℝ), (73737801/156250000 : ℝ)] ![(16523919418569/50000000000000 : ℝ), (26641276754121/100000000000000 : ℝ), (40310884398289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(400458811/1000000000 : ℝ)|^5903 ≤ (16523919418569/50000000000000 : ℝ)^4879
        have hw : |(400458811/1000000000 : ℝ)|=(400458811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26181509/78125000 : ℝ)|^5903 ≤ (26641276754121/100000000000000 : ℝ)^4879
        have hw : |(26181509/78125000 : ℝ)|=(26181509/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73737801/156250000 : ℝ)|^5903 ≤ (40310884398289/100000000000000 : ℝ)^4879
        have hw : |(73737801/156250000 : ℝ)|=(73737801/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_4 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1179320913/10000000000 : ℝ)*x 0 + (5089908797/10000000000 : ℝ)*x 1 + (5479660707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1179320913/10000000000 : ℝ)^5903 ≤ (7529861432343/100000000000000 : ℝ)^4879 := by
    have hnat : (1179320913 : ℕ)^5903*100000000000000^4879 ≤ 7529861432343^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179320913 10000000000 7529861432343 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089908797/10000000000 : ℝ)^5903 ≤ (44172763203889/100000000000000 : ℝ)^4879 := by
    have hnat : (5089908797 : ℕ)^5903*100000000000000^4879 ≤ 44172763203889^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089908797 10000000000 44172763203889 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479660707/10000000000 : ℝ)^5903 ≤ (24148687678121/50000000000000 : ℝ)^4879 := by
    have hnat : (5479660707 : ℕ)^5903*50000000000000^4879 ≤ 24148687678121^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479660707 10000000000 24148687678121 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1179320913/10000000000 : ℝ), (5089908797/10000000000 : ℝ), (5479660707/10000000000 : ℝ)] ![(7529861432343/100000000000000 : ℝ), (44172763203889/100000000000000 : ℝ), (24148687678121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1179320913/10000000000 : ℝ)|^5903 ≤ (7529861432343/100000000000000 : ℝ)^4879
        have hw : |(-1179320913/10000000000 : ℝ)|=(1179320913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089908797/10000000000 : ℝ)|^5903 ≤ (44172763203889/100000000000000 : ℝ)^4879
        have hw : |(5089908797/10000000000 : ℝ)|=(5089908797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479660707/10000000000 : ℝ)|^5903 ≤ (24148687678121/50000000000000 : ℝ)^4879
        have hw : |(5479660707/10000000000 : ℝ)|=(5479660707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_5 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653012023/1250000000 : ℝ)*x 0 + (-993209127/10000000000 : ℝ)*x 1 + (5479660959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653012023/1250000000 : ℝ)^5903 ≤ (45585593013979/100000000000000 : ℝ)^4879 := by
    have hnat : (653012023 : ℕ)^5903*100000000000000^4879 ≤ 45585593013979^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653012023 1250000000 45585593013979 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993209127/10000000000 : ℝ)^5903 ≤ (611702891593/10000000000000 : ℝ)^4879 := by
    have hnat : (993209127 : ℕ)^5903*10000000000000^4879 ≤ 611702891593^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993209127 10000000000 611702891593 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479660959/10000000000 : ℝ)^5903 ≤ (48297378043519/100000000000000 : ℝ)^4879 := by
    have hnat : (5479660959 : ℕ)^5903*100000000000000^4879 ≤ 48297378043519^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479660959 10000000000 48297378043519 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653012023/1250000000 : ℝ), (-993209127/10000000000 : ℝ), (5479660959/10000000000 : ℝ)] ![(45585593013979/100000000000000 : ℝ), (611702891593/10000000000000 : ℝ), (48297378043519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653012023/1250000000 : ℝ)|^5903 ≤ (45585593013979/100000000000000 : ℝ)^4879
        have hw : |(653012023/1250000000 : ℝ)|=(653012023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993209127/10000000000 : ℝ)|^5903 ≤ (611702891593/10000000000000 : ℝ)^4879
        have hw : |(-993209127/10000000000 : ℝ)|=(993209127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479660959/10000000000 : ℝ)|^5903 ≤ (48297378043519/100000000000000 : ℝ)^4879
        have hw : |(5479660959/10000000000 : ℝ)|=(5479660959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_6 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326506049/625000000 : ℝ)*x 0 + (1095932047/2000000000 : ℝ)*x 1 + (-496604657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326506049/625000000 : ℝ)^5903 ≤ (1139639983711/2500000000000 : ℝ)^4879 := by
    have hnat : (326506049 : ℕ)^5903*2500000000000^4879 ≤ 1139639983711^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326506049 625000000 1139639983711 2500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095932047/2000000000 : ℝ)^5903 ≤ (48297370322931/100000000000000 : ℝ)^4879 := by
    have hnat : (1095932047 : ℕ)^5903*100000000000000^4879 ≤ 48297370322931^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095932047 2000000000 48297370322931 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496604657/5000000000 : ℝ)^5903 ≤ (1223406061871/20000000000000 : ℝ)^4879 := by
    have hnat : (496604657 : ℕ)^5903*20000000000000^4879 ≤ 1223406061871^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496604657 5000000000 1223406061871 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326506049/625000000 : ℝ), (1095932047/2000000000 : ℝ), (-496604657/5000000000 : ℝ)] ![(1139639983711/2500000000000 : ℝ), (48297370322931/100000000000000 : ℝ), (1223406061871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326506049/625000000 : ℝ)|^5903 ≤ (1139639983711/2500000000000 : ℝ)^4879
        have hw : |(326506049/625000000 : ℝ)|=(326506049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095932047/2000000000 : ℝ)|^5903 ≤ (48297370322931/100000000000000 : ℝ)^4879
        have hw : |(1095932047/2000000000 : ℝ)|=(1095932047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496604657/5000000000 : ℝ)|^5903 ≤ (1223406061871/20000000000000 : ℝ)^4879
        have hw : |(-496604657/5000000000 : ℝ)|=(496604657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_s3_7 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1001430989/2500000000 : ℝ)*x 0 + (2348340707/5000000000 : ℝ)*x 1 + (210890123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001430989/2500000000 : ℝ)^5903 ≤ (16529590025683/50000000000000 : ℝ)^4879 := by
    have hnat : (1001430989 : ℕ)^5903*50000000000000^4879 ≤ 16529590025683^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001430989 2500000000 16529590025683 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2348340707/5000000000 : ℝ)^5903 ≤ (1603123254547/4000000000000 : ℝ)^4879 := by
    have hnat : (2348340707 : ℕ)^5903*4000000000000^4879 ≤ 1603123254547^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348340707 5000000000 1603123254547 4000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210890123/625000000 : ℝ)^5903 ≤ (6715684642389/25000000000000 : ℝ)^4879 := by
    have hnat : (210890123 : ℕ)^5903*25000000000000^4879 ≤ 6715684642389^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210890123 625000000 6715684642389 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001430989/2500000000 : ℝ), (2348340707/5000000000 : ℝ), (210890123/625000000 : ℝ)] ![(16529590025683/50000000000000 : ℝ), (1603123254547/4000000000000 : ℝ), (6715684642389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001430989/2500000000 : ℝ)|^5903 ≤ (16529590025683/50000000000000 : ℝ)^4879
        have hw : |(1001430989/2500000000 : ℝ)|=(1001430989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2348340707/5000000000 : ℝ)|^5903 ≤ (1603123254547/4000000000000 : ℝ)^4879
        have hw : |(2348340707/5000000000 : ℝ)|=(2348340707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210890123/625000000 : ℝ)|^5903 ≤ (6715684642389/25000000000000 : ℝ)^4879
        have hw : |(210890123/625000000 : ℝ)|=(210890123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1758_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1827/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (891/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4567/50000 : ℝ) ^ (5887/1024 : ℝ) ≤ (52940224131501/50000000000000000000 : ℝ) := by
    have hpowers : (4567/50000 : ℝ)^5887 ≤ (52940224131501/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4567 : ℕ)^5887*50000000000000000000^1024 ≤ 52940224131501^1024*50000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4567 50000 52940224131501 50000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4567/50000 : ℝ)) (X := (52940224131501/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17821/100000 : ℝ) ^ (5887/1024 : ℝ) ≤ (4938452891091831/100000000000000000000 : ℝ) := by
    have hpowers : (17821/100000 : ℝ)^5887 ≤ (4938452891091831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17821 : ℕ)^5887*100000000000000000000^1024 ≤ 4938452891091831^1024*100000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17821 100000 4938452891091831 100000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17821/100000 : ℝ)) (X := (4938452891091831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000052940224131501/25000000000000000000 : ℝ) ≤ (10000003683420561/10000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (25000052940224131501/25000000000000000000 : ℝ)^1024 ≤ (10000003683420561/10000000000000000 : ℝ)^5887 := by
      have hnat : (25000052940224131501 : ℕ)^1024*10000000000000000^5887 ≤ 10000003683420561^5887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000052940224131501 25000000000000000000 10000003683420561 10000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003683420561/10000000000000000 : ℝ)) (X := (25000052940224131501/25000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005044333339354833/100000000000000000000 : ℝ) ≤ (2500021935152557/2500000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (100005044333339354833/100000000000000000000 : ℝ)^1024 ≤ (2500021935152557/2500000000000000 : ℝ)^5887 := by
      have hnat : (100005044333339354833 : ℕ)^1024*2500000000000000^5887 ≤ 2500021935152557^5887*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005044333339354833 100000000000000000000 2500021935152557 2500000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500021935152557/2500000000000000 : ℝ)) (X := (100005044333339354833/100000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004938452891091831/50000000000000000000 : ℝ) ≤ (2000034359559979/2000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50004938452891091831/50000000000000000000 : ℝ)^1024 ≤ (2000034359559979/2000000000000000 : ℝ)^5887 := by
      have hnat : (50004938452891091831 : ℕ)^1024*2000000000000000^5887 ≤ 2000034359559979^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004938452891091831 50000000000000000000 2000034359559979 2000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000034359559979/2000000000000000 : ℝ)) (X := (50004938452891091831/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52940224131501/50000000000000000000 : ℝ) ≤ ((86868496441133576651/86870000000000000000 : ℝ)+2*(84057189667/868700000000000 : ℝ)*(4567/50000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (86868496441133576651/86870000000000000000 : ℝ)+2*(84057189667/868700000000000 : ℝ)*(4567/50000 : ℝ)=(10000003683420561/10000000000000000 : ℝ) by norm_num, show 1+2*(52940224131501/50000000000000000000 : ℝ)=(25000052940224131501/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4938452891091831/100000000000000000000 : ℝ)+(52940224131501/50000000000000000000 : ℝ) ≤ ((86868496441133576651/86870000000000000000 : ℝ)+(84057189667/868700000000000 : ℝ)*((17821/100000 : ℝ)+(4567/50000 : ℝ)))^(5887/1024 : ℝ) := by
    rw [show (86868496441133576651/86870000000000000000 : ℝ)+(84057189667/868700000000000 : ℝ)*((17821/100000 : ℝ)+(4567/50000 : ℝ))=(2500021935152557/2500000000000000 : ℝ) by norm_num, show 1+(4938452891091831/100000000000000000000 : ℝ)+(52940224131501/50000000000000000000 : ℝ)=(100005044333339354833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4938452891091831/100000000000000000000 : ℝ) ≤ ((86868496441133576651/86870000000000000000 : ℝ)+2*(84057189667/868700000000000 : ℝ)*(17821/100000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (86868496441133576651/86870000000000000000 : ℝ)+2*(84057189667/868700000000000 : ℝ)*(17821/100000 : ℝ)=(2000034359559979/2000000000000000 : ℝ) by norm_num, show 1+2*(4938452891091831/100000000000000000000 : ℝ)=(50004938452891091831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86868496441133576651/86870000000000000000 : ℝ)*(X 1 0+X 2 0)+(84057189667/868700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4567/50000 : ℝ)) (hi := (17821/100000 : ℝ)) (c := (86868496441133576651/86870000000000000000 : ℝ)) (alpha := (84057189667/868700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86868496441133576651/86870000000000000000 : ℝ)*(X 0 1+X 2 1)+(84057189667/868700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4567/50000 : ℝ)) (hi := (17821/100000 : ℝ)) (c := (86868496441133576651/86870000000000000000 : ℝ)) (alpha := (84057189667/868700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86868496441133576651/86870000000000000000 : ℝ)*(X 0 2+X 1 2)+(84057189667/868700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (4567/50000 : ℝ)) (hi := (17821/100000 : ℝ)) (c := (86868496441133576651/86870000000000000000 : ℝ)) (alpha := (84057189667/868700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1178986097/10000000000 : ℝ)*X 0 0+(1371610423/2500000000 : ℝ)*X 0 1+(1016653301/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2665357449/5000000000 : ℝ)*X 1 0+(-1389603419/10000000000 : ℝ)*X 1 1+(1016653299/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106614299/200000000 : ℝ)*X 2 0+(635408309/1250000000 : ℝ)*X 2 1+(-1389603381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((400458811/1000000000 : ℝ)*X 0 0+(26181509/78125000 : ℝ)*X 0 1+(73737801/156250000 : ℝ)*X 0 2+(400458811/1000000000 : ℝ)*X 1 0+(26181509/78125000 : ℝ)*X 1 1+(73737801/156250000 : ℝ)*X 1 2+(400458811/1000000000 : ℝ)*X 2 0+(26181509/78125000 : ℝ)*X 2 1+(73737801/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1179320913/10000000000 : ℝ)*X 0 0+(5089908797/10000000000 : ℝ)*X 0 1+(5479660707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((653012023/1250000000 : ℝ)*X 1 0+(-993209127/10000000000 : ℝ)*X 1 1+(5479660959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((326506049/625000000 : ℝ)*X 2 0+(1095932047/2000000000 : ℝ)*X 2 1+(-496604657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1001430989/2500000000 : ℝ)*X 0 0+(2348340707/5000000000 : ℝ)*X 0 1+(210890123/625000000 : ℝ)*X 0 2+(1001430989/2500000000 : ℝ)*X 1 0+(2348340707/5000000000 : ℝ)*X 1 1+(210890123/625000000 : ℝ)*X 1 2+(1001430989/2500000000 : ℝ)*X 2 0+(2348340707/5000000000 : ℝ)*X 2 1+(210890123/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1669610081733694197673596519/542937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85490381/20000000000000 : ℝ)*(base19) + (8504941/2000000000000 : ℝ)*(base23) + (14072999/100000000000000 : ℝ)*(lower2) + (6299391/10000000000000 : ℝ)*(upper3) + (67393389/100000000000000 : ℝ)*(upper5) + (401415243910777/25000000000000 : ℝ)*(major0) + (401415243910777/25000000000000 : ℝ)*(major1) + (401415243910777/25000000000000 : ℝ)*(major2) + (310039327518257/12500000000000 : ℝ)*(sp0) + (1240158921455527/50000000000000 : ℝ)*(sp1) + (2480317845115909/100000000000000 : ℝ)*(sp2) + (731002541299221/100000000000000 : ℝ)*(sp3) + (3650216903/100000000000000 : ℝ)*(sp4) + (259279821/25000000000000 : ℝ)*(sp7) + (146200715683701/20000000000000 : ℝ)*(f.failure) + (2480318270362959/100000000000000 : ℝ)*(f.sum) + (193152651350831/43435000000000000000000000000 : ℝ)*base65 + (3127971538131588261/310250000000000000000000000000000 : ℝ)*base67 + (3020480974785088261/310250000000000000000000000000000 : ℝ)*base69 + (83732644242161739/310250000000000000000000000000000 : ℝ)*base72 + (105488870621633/21717500000000000000000000000 : ℝ)*base73 + (1781233568037838261/310250000000000000000000000000000 : ℝ)*base75 + (2602270053513338261/310250000000000000000000000000000 : ℝ)*base77 + (376692965430338261/310250000000000000000000000000000 : ℝ)*base79 + (60538560575791/43435000000000000000000000000 : ℝ)*base81 + (13949111/2000000000000000000000 : ℝ)*base90 + (13949111/2000000000000000000000 : ℝ)*base92 + (13949111/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610601519193877968567147411/155125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101063989/25000000000000 : ℝ)*(base19) + (666134773/100000000000000 : ℝ)*(base23) + (141951931/100000000000000 : ℝ)*(lower1) + (15728329/50000000000000 : ℝ)*(upper3) + (1382001/50000000000000 : ℝ)*(lower4) + (1601283/1562500000000 : ℝ)*(upper5) + (830477478989109/50000000000000 : ℝ)*(major0) + (830477478989109/50000000000000 : ℝ)*(major1) + (830477478989109/50000000000000 : ℝ)*(major2) + (1866455747/100000000000000 : ℝ)*(sp1) + (1282866355538139/50000000000000 : ℝ)*(sp4) + (1282865220182287/50000000000000 : ℝ)*(sp5) + (40089563202211/1562500000000 : ℝ)*(sp6) + (756177073673807/100000000000000 : ℝ)*(sp7) + (756177073673807/100000000000000 : ℝ)*(f.failure) + (1282866355538139/50000000000000 : ℝ)*(f.sum) + (6387837835517/1551250000000000000000000000 : ℝ)*base65 + (3850386697624000863/620500000000000000000000000000000 : ℝ)*base68 + (6857205633613000863/620500000000000000000000000000000 : ℝ)*base70 + (831978125250999137/620500000000000000000000000000000 : ℝ)*base71 + (11640743269623/6205000000000000000000000000 : ℝ)*base73 + (8571867215655500863/620500000000000000000000000000000 : ℝ)*base76 + (3462948336786000863/620500000000000000000000000000000 : ℝ)*base78 + (1144805577441000863/620500000000000000000000000000000 : ℝ)*base80 + (2481628942271/3102500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24770677/10000000000000000000000 : ℝ)*base90 + (24770677/10000000000000000000000 : ℝ)*base92 + (24770677/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1758_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1827/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (891/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1758_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1758_box_0 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-805086617/10000000000 : ℝ)*x 0 + (5416784519/10000000000 : ℝ)*x 1 + (5416784763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (805086617/10000000000 : ℝ)^5903 ≤ (4744624722717/100000000000000 : ℝ)^4879 := by
    have hnat : (805086617 : ℕ)^5903*100000000000000^4879 ≤ 4744624722717^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805086617 10000000000 4744624722717 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416784519/10000000000 : ℝ)^5903 ≤ (47627686333311/100000000000000 : ℝ)^4879 := by
    have hnat : (5416784519 : ℕ)^5903*100000000000000^4879 ≤ 47627686333311^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416784519 10000000000 47627686333311 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416784763/10000000000 : ℝ)^5903 ≤ (23813844464491/50000000000000 : ℝ)^4879 := by
    have hnat : (5416784763 : ℕ)^5903*50000000000000^4879 ≤ 23813844464491^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416784763 10000000000 23813844464491 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-805086617/10000000000 : ℝ), (5416784519/10000000000 : ℝ), (5416784763/10000000000 : ℝ)] ![(4744624722717/100000000000000 : ℝ), (47627686333311/100000000000000 : ℝ), (23813844464491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-805086617/10000000000 : ℝ)|^5903 ≤ (4744624722717/100000000000000 : ℝ)^4879
        have hw : |(-805086617/10000000000 : ℝ)|=(805086617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416784519/10000000000 : ℝ)|^5903 ≤ (47627686333311/100000000000000 : ℝ)^4879
        have hw : |(5416784519/10000000000 : ℝ)|=(5416784519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416784763/10000000000 : ℝ)|^5903 ≤ (23813844464491/50000000000000 : ℝ)^4879
        have hw : |(5416784763/10000000000 : ℝ)|=(5416784763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_1 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193526961/10000000000 : ℝ)*x 0 + (-140575423/1250000000 : ℝ)*x 1 + (5416784611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193526961/10000000000 : ℝ)^5903 ≤ (45263058918251/100000000000000 : ℝ)^4879 := by
    have hnat : (5193526961 : ℕ)^5903*100000000000000^4879 ≤ 45263058918251^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193526961 10000000000 45263058918251 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140575423/1250000000 : ℝ)^5903 ≤ (7109253759123/100000000000000 : ℝ)^4879 := by
    have hnat : (140575423 : ℕ)^5903*100000000000000^4879 ≤ 7109253759123^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140575423 1250000000 7109253759123 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416784611/10000000000 : ℝ)^5903 ≤ (47627687312007/100000000000000 : ℝ)^4879 := by
    have hnat : (5416784611 : ℕ)^5903*100000000000000^4879 ≤ 47627687312007^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416784611 10000000000 47627687312007 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193526961/10000000000 : ℝ), (-140575423/1250000000 : ℝ), (5416784611/10000000000 : ℝ)] ![(45263058918251/100000000000000 : ℝ), (7109253759123/100000000000000 : ℝ), (47627687312007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193526961/10000000000 : ℝ)|^5903 ≤ (45263058918251/100000000000000 : ℝ)^4879
        have hw : |(5193526961/10000000000 : ℝ)|=(5193526961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140575423/1250000000 : ℝ)|^5903 ≤ (7109253759123/100000000000000 : ℝ)^4879
        have hw : |(-140575423/1250000000 : ℝ)|=(140575423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416784611/10000000000 : ℝ)|^5903 ≤ (47627687312007/100000000000000 : ℝ)^4879
        have hw : |(5416784611/10000000000 : ℝ)|=(5416784611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_2 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649190857/1250000000 : ℝ)*x 0 + (2708392373/5000000000 : ℝ)*x 1 + (-56230167/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649190857/1250000000 : ℝ)^5903 ≤ (9052611562217/20000000000000 : ℝ)^4879 := by
    have hnat : (649190857 : ℕ)^5903*20000000000000^4879 ≤ 9052611562217^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649190857 1250000000 9052611562217 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708392373/5000000000 : ℝ)^5903 ≤ (5953461093517/12500000000000 : ℝ)^4879 := by
    have hnat : (2708392373 : ℕ)^5903*12500000000000^4879 ≤ 5953461093517^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708392373 5000000000 5953461093517 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56230167/500000000 : ℝ)^5903 ≤ (1777313355649/25000000000000 : ℝ)^4879 := by
    have hnat : (56230167 : ℕ)^5903*25000000000000^4879 ≤ 1777313355649^4879*500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56230167 500000000 1777313355649 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649190857/1250000000 : ℝ), (2708392373/5000000000 : ℝ), (-56230167/500000000 : ℝ)] ![(9052611562217/20000000000000 : ℝ), (5953461093517/12500000000000 : ℝ), (1777313355649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649190857/1250000000 : ℝ)|^5903 ≤ (9052611562217/20000000000000 : ℝ)^4879
        have hw : |(649190857/1250000000 : ℝ)|=(649190857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708392373/5000000000 : ℝ)|^5903 ≤ (5953461093517/12500000000000 : ℝ)^4879
        have hw : |(2708392373/5000000000 : ℝ)|=(2708392373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56230167/500000000 : ℝ)|^5903 ≤ (1777313355649/25000000000000 : ℝ)^4879
        have hw : |(-56230167/500000000 : ℝ)|=(56230167/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_3 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1132420481/2500000000 : ℝ)*x 0 + (945024109/2500000000 : ℝ)*x 1 + (3780096421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132420481/2500000000 : ℝ)^5903 ≤ (19180217161513/50000000000000 : ℝ)^4879 := by
    have hnat : (1132420481 : ℕ)^5903*50000000000000^4879 ≤ 19180217161513^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132420481 2500000000 19180217161513 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945024109/2500000000 : ℝ)^5903 ≤ (3852472863397/12500000000000 : ℝ)^4879 := by
    have hnat : (945024109 : ℕ)^5903*12500000000000^4879 ≤ 3852472863397^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945024109 2500000000 3852472863397 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3780096421/10000000000 : ℝ)^5903 ≤ (3081978275921/10000000000000 : ℝ)^4879 := by
    have hnat : (3780096421 : ℕ)^5903*10000000000000^4879 ≤ 3081978275921^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780096421 10000000000 3081978275921 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1132420481/2500000000 : ℝ), (945024109/2500000000 : ℝ), (3780096421/10000000000 : ℝ)] ![(19180217161513/50000000000000 : ℝ), (3852472863397/12500000000000 : ℝ), (3081978275921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1132420481/2500000000 : ℝ)|^5903 ≤ (19180217161513/50000000000000 : ℝ)^4879
        have hw : |(1132420481/2500000000 : ℝ)|=(1132420481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(945024109/2500000000 : ℝ)|^5903 ≤ (3852472863397/12500000000000 : ℝ)^4879
        have hw : |(945024109/2500000000 : ℝ)|=(945024109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3780096421/10000000000 : ℝ)|^5903 ≤ (3081978275921/10000000000000 : ℝ)^4879
        have hw : |(3780096421/10000000000 : ℝ)|=(3780096421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_4 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398018271/2500000000 : ℝ)*x 0 + (2564661853/5000000000 : ℝ)*x 1 + (641165487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398018271/2500000000 : ℝ)^5903 ≤ (5413046255479/50000000000000 : ℝ)^4879 := by
    have hnat : (398018271 : ℕ)^5903*50000000000000^4879 ≤ 5413046255479^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398018271 2500000000 5413046255479 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564661853/5000000000 : ℝ)^5903 ≤ (22293476367699/50000000000000 : ℝ)^4879 := by
    have hnat : (2564661853 : ℕ)^5903*50000000000000^4879 ≤ 22293476367699^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564661853 5000000000 22293476367699 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641165487/1250000000 : ℝ)^5903 ≤ (22293477366809/50000000000000 : ℝ)^4879 := by
    have hnat : (641165487 : ℕ)^5903*50000000000000^4879 ≤ 22293477366809^4879*1250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641165487 1250000000 22293477366809 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398018271/2500000000 : ℝ), (2564661853/5000000000 : ℝ), (641165487/1250000000 : ℝ)] ![(5413046255479/50000000000000 : ℝ), (22293476367699/50000000000000 : ℝ), (22293477366809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398018271/2500000000 : ℝ)|^5903 ≤ (5413046255479/50000000000000 : ℝ)^4879
        have hw : |(-398018271/2500000000 : ℝ)|=(398018271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564661853/5000000000 : ℝ)|^5903 ≤ (22293476367699/50000000000000 : ℝ)^4879
        have hw : |(2564661853/5000000000 : ℝ)|=(2564661853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641165487/1250000000 : ℝ)|^5903 ≤ (22293477366809/50000000000000 : ℝ)^4879
        have hw : |(641165487/1250000000 : ℝ)|=(641165487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_5 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385316659/10000000000 : ℝ)*x 0 + (-627599473/5000000000 : ℝ)*x 1 + (5129323891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385316659/10000000000 : ℝ)^5903 ≤ (23646567850709/50000000000000 : ℝ)^4879 := by
    have hnat : (5385316659 : ℕ)^5903*50000000000000^4879 ≤ 23646567850709^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385316659 10000000000 23646567850709 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627599473/5000000000 : ℝ)^5903 ≤ (253747174993/3125000000000 : ℝ)^4879 := by
    have hnat : (627599473 : ℕ)^5903*3125000000000^4879 ≤ 253747174993^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627599473 5000000000 253747174993 3125000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129323891/10000000000 : ℝ)^5903 ≤ (44586954681033/100000000000000 : ℝ)^4879 := by
    have hnat : (5129323891 : ℕ)^5903*100000000000000^4879 ≤ 44586954681033^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129323891 10000000000 44586954681033 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385316659/10000000000 : ℝ), (-627599473/5000000000 : ℝ), (5129323891/10000000000 : ℝ)] ![(23646567850709/50000000000000 : ℝ), (253747174993/3125000000000 : ℝ), (44586954681033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385316659/10000000000 : ℝ)|^5903 ≤ (23646567850709/50000000000000 : ℝ)^4879
        have hw : |(5385316659/10000000000 : ℝ)|=(5385316659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627599473/5000000000 : ℝ)|^5903 ≤ (253747174993/3125000000000 : ℝ)^4879
        have hw : |(-627599473/5000000000 : ℝ)|=(627599473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129323891/10000000000 : ℝ)|^5903 ≤ (44586954681033/100000000000000 : ℝ)^4879
        have hw : |(5129323891/10000000000 : ℝ)|=(5129323891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_6 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385316851/10000000000 : ℝ)*x 0 + (5129323831/10000000000 : ℝ)*x 1 + (-1255198767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385316851/10000000000 : ℝ)^5903 ≤ (23646568870709/50000000000000 : ℝ)^4879 := by
    have hnat : (5385316851 : ℕ)^5903*50000000000000^4879 ≤ 23646568870709^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385316851 10000000000 23646568870709 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129323831/10000000000 : ℝ)^5903 ≤ (1393342314063/3125000000000 : ℝ)^4879 := by
    have hnat : (5129323831 : ℕ)^5903*3125000000000^4879 ≤ 1393342314063^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129323831 10000000000 1393342314063 3125000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255198767/10000000000 : ℝ)^5903 ≤ (811990819879/10000000000000 : ℝ)^4879 := by
    have hnat : (1255198767 : ℕ)^5903*10000000000000^4879 ≤ 811990819879^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255198767 10000000000 811990819879 10000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385316851/10000000000 : ℝ), (5129323831/10000000000 : ℝ), (-1255198767/10000000000 : ℝ)] ![(23646568870709/50000000000000 : ℝ), (1393342314063/3125000000000 : ℝ), (811990819879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385316851/10000000000 : ℝ)|^5903 ≤ (23646568870709/50000000000000 : ℝ)^4879
        have hw : |(5385316851/10000000000 : ℝ)|=(5385316851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129323831/10000000000 : ℝ)|^5903 ≤ (1393342314063/3125000000000 : ℝ)^4879
        have hw : |(5129323831/10000000000 : ℝ)|=(5129323831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1255198767/10000000000 : ℝ)|^5903 ≤ (811990819879/10000000000000 : ℝ)^4879
        have hw : |(-1255198767/10000000000 : ℝ)|=(1255198767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_7 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3441502343/10000000000 : ℝ)*x 0 + (4322113917/10000000000 : ℝ)*x 1 + (4322114347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3441502343/10000000000 : ℝ)^5903 ≤ (3438992245743/12500000000000 : ℝ)^4879 := by
    have hnat : (3441502343 : ℕ)^5903*12500000000000^4879 ≤ 3438992245743^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3441502343 10000000000 3438992245743 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4322113917/10000000000 : ℝ)^5903 ≤ (36244028831601/100000000000000 : ℝ)^4879 := by
    have hnat : (4322113917 : ℕ)^5903*100000000000000^4879 ≤ 36244028831601^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322113917 10000000000 36244028831601 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4322114347/10000000000 : ℝ)^5903 ≤ (18122016597127/50000000000000 : ℝ)^4879 := by
    have hnat : (4322114347 : ℕ)^5903*50000000000000^4879 ≤ 18122016597127^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322114347 10000000000 18122016597127 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3441502343/10000000000 : ℝ), (4322113917/10000000000 : ℝ), (4322114347/10000000000 : ℝ)] ![(3438992245743/12500000000000 : ℝ), (36244028831601/100000000000000 : ℝ), (18122016597127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3441502343/10000000000 : ℝ)|^5903 ≤ (3438992245743/12500000000000 : ℝ)^4879
        have hw : |(3441502343/10000000000 : ℝ)|=(3441502343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4322113917/10000000000 : ℝ)|^5903 ≤ (36244028831601/100000000000000 : ℝ)^4879
        have hw : |(4322113917/10000000000 : ℝ)|=(4322113917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4322114347/10000000000 : ℝ)|^5903 ≤ (18122016597127/50000000000000 : ℝ)^4879
        have hw : |(4322114347/10000000000 : ℝ)|=(4322114347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_8 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1420726149/10000000000 : ℝ)*x 0 + (490964681/1000000000 : ℝ)*x 1 + (342377467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1420726149/10000000000 : ℝ)^5903 ≤ (1179098397979/12500000000000 : ℝ)^4879 := by
    have hnat : (1420726149 : ℕ)^5903*12500000000000^4879 ≤ 1179098397979^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420726149 10000000000 1179098397979 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490964681/1000000000 : ℝ)^5903 ≤ (42287125425197/100000000000000 : ℝ)^4879 := by
    have hnat : (490964681 : ℕ)^5903*100000000000000^4879 ≤ 42287125425197^4879*1000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490964681 1000000000 42287125425197 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342377467/625000000 : ℝ)^5903 ≤ (241400436869/500000000000 : ℝ)^4879 := by
    have hnat : (342377467 : ℕ)^5903*500000000000^4879 ≤ 241400436869^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342377467 625000000 241400436869 500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1420726149/10000000000 : ℝ), (490964681/1000000000 : ℝ), (342377467/625000000 : ℝ)] ![(1179098397979/12500000000000 : ℝ), (42287125425197/100000000000000 : ℝ), (241400436869/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1420726149/10000000000 : ℝ)|^5903 ≤ (1179098397979/12500000000000 : ℝ)^4879
        have hw : |(-1420726149/10000000000 : ℝ)|=(1420726149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(490964681/1000000000 : ℝ)|^5903 ≤ (42287125425197/100000000000000 : ℝ)^4879
        have hw : |(490964681/1000000000 : ℝ)|=(490964681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342377467/625000000 : ℝ)|^5903 ≤ (241400436869/500000000000 : ℝ)^4879
        have hw : |(342377467/625000000 : ℝ)|=(342377467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_9 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (322045741/625000000 : ℝ)*x 0 + (-1095419687/10000000000 : ℝ)*x 1 + (5478039529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322045741/625000000 : ℝ)^5903 ≤ (44833252743429/100000000000000 : ℝ)^4879 := by
    have hnat : (322045741 : ℕ)^5903*100000000000000^4879 ≤ 44833252743429^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322045741 625000000 44833252743429 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095419687/10000000000 : ℝ)^5903 ≤ (86083240819/1250000000000 : ℝ)^4879 := by
    have hnat : (1095419687 : ℕ)^5903*1250000000000^4879 ≤ 86083240819^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095419687 10000000000 86083240819 1250000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478039529/10000000000 : ℝ)^5903 ≤ (24140043990799/50000000000000 : ℝ)^4879 := by
    have hnat : (5478039529 : ℕ)^5903*50000000000000^4879 ≤ 24140043990799^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478039529 10000000000 24140043990799 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322045741/625000000 : ℝ), (-1095419687/10000000000 : ℝ), (5478039529/10000000000 : ℝ)] ![(44833252743429/100000000000000 : ℝ), (86083240819/1250000000000 : ℝ), (24140043990799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322045741/625000000 : ℝ)|^5903 ≤ (44833252743429/100000000000000 : ℝ)^4879
        have hw : |(322045741/625000000 : ℝ)|=(322045741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095419687/10000000000 : ℝ)|^5903 ≤ (86083240819/1250000000000 : ℝ)^4879
        have hw : |(-1095419687/10000000000 : ℝ)|=(1095419687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478039529/10000000000 : ℝ)|^5903 ≤ (24140043990799/50000000000000 : ℝ)^4879
        have hw : |(5478039529/10000000000 : ℝ)|=(5478039529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_10 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515273191/1000000000 : ℝ)*x 0 + (5478039787/10000000000 : ℝ)*x 1 + (-4381677/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515273191/1000000000 : ℝ)^5903 ≤ (44833253311887/100000000000000 : ℝ)^4879 := by
    have hnat : (515273191 : ℕ)^5903*100000000000000^4879 ≤ 44833253311887^4879*1000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515273191 1000000000 44833253311887 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478039787/10000000000 : ℝ)^5903 ≤ (48280090732687/100000000000000 : ℝ)^4879 := by
    have hnat : (5478039787 : ℕ)^5903*100000000000000^4879 ≤ 48280090732687^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478039787 10000000000 48280090732687 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381677/40000000 : ℝ)^5903 ≤ (3443327970797/50000000000000 : ℝ)^4879 := by
    have hnat : (4381677 : ℕ)^5903*50000000000000^4879 ≤ 3443327970797^4879*40000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381677 40000000 3443327970797 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515273191/1000000000 : ℝ), (5478039787/10000000000 : ℝ), (-4381677/40000000 : ℝ)] ![(44833253311887/100000000000000 : ℝ), (48280090732687/100000000000000 : ℝ), (3443327970797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515273191/1000000000 : ℝ)|^5903 ≤ (44833253311887/100000000000000 : ℝ)^4879
        have hw : |(515273191/1000000000 : ℝ)|=(515273191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478039787/10000000000 : ℝ)|^5903 ≤ (48280090732687/100000000000000 : ℝ)^4879
        have hw : |(5478039787/10000000000 : ℝ)|=(5478039787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4381677/40000000 : ℝ)|^5903 ≤ (3443327970797/50000000000000 : ℝ)^4879
        have hw : |(-4381677/40000000 : ℝ)|=(4381677/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_11 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (190042241/400000000 : ℝ)*x 0 + (1832084373/5000000000 : ℝ)*x 1 + (732833331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190042241/400000000 : ℝ)^5903 ≤ (10160034363677/25000000000000 : ℝ)^4879 := by
    have hnat : (190042241 : ℕ)^5903*25000000000000^4879 ≤ 10160034363677^4879*400000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190042241 400000000 10160034363677 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1832084373/5000000000 : ℝ)^5903 ≤ (29679941511899/100000000000000 : ℝ)^4879 := by
    have hnat : (1832084373 : ℕ)^5903*100000000000000^4879 ≤ 29679941511899^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832084373 5000000000 29679941511899 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732833331/2000000000 : ℝ)^5903 ≤ (927497531873/3125000000000 : ℝ)^4879 := by
    have hnat : (732833331 : ℕ)^5903*3125000000000^4879 ≤ 927497531873^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732833331 2000000000 927497531873 3125000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(190042241/400000000 : ℝ), (1832084373/5000000000 : ℝ), (732833331/2000000000 : ℝ)] ![(10160034363677/25000000000000 : ℝ), (29679941511899/100000000000000 : ℝ), (927497531873/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(190042241/400000000 : ℝ)|^5903 ≤ (10160034363677/25000000000000 : ℝ)^4879
        have hw : |(190042241/400000000 : ℝ)|=(190042241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1832084373/5000000000 : ℝ)|^5903 ≤ (29679941511899/100000000000000 : ℝ)^4879
        have hw : |(1832084373/5000000000 : ℝ)|=(1832084373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(732833331/2000000000 : ℝ)|^5903 ≤ (927497531873/3125000000000 : ℝ)^4879
        have hw : |(732833331/2000000000 : ℝ)|=(732833331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_12 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-481140951/5000000000 : ℝ)*x 0 + (5623880003/10000000000 : ℝ)*x 1 + (5099467237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481140951/5000000000 : ℝ)^5903 ≤ (1471833755591/25000000000000 : ℝ)^4879 := by
    have hnat : (481140951 : ℕ)^5903*25000000000000^4879 ≤ 1471833755591^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481140951 5000000000 1471833755591 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5623880003/10000000000 : ℝ)^5903 ≤ (49839519006153/100000000000000 : ℝ)^4879 := by
    have hnat : (5623880003 : ℕ)^5903*100000000000000^4879 ≤ 49839519006153^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5623880003 10000000000 49839519006153 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099467237/10000000000 : ℝ)^5903 ≤ (44273145952931/100000000000000 : ℝ)^4879 := by
    have hnat : (5099467237 : ℕ)^5903*100000000000000^4879 ≤ 44273145952931^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099467237 10000000000 44273145952931 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481140951/5000000000 : ℝ), (5623880003/10000000000 : ℝ), (5099467237/10000000000 : ℝ)] ![(1471833755591/25000000000000 : ℝ), (49839519006153/100000000000000 : ℝ), (44273145952931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481140951/5000000000 : ℝ)|^5903 ≤ (1471833755591/25000000000000 : ℝ)^4879
        have hw : |(-481140951/5000000000 : ℝ)|=(481140951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5623880003/10000000000 : ℝ)|^5903 ≤ (49839519006153/100000000000000 : ℝ)^4879
        have hw : |(5623880003/10000000000 : ℝ)|=(5623880003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099467237/10000000000 : ℝ)|^5903 ≤ (44273145952931/100000000000000 : ℝ)^4879
        have hw : |(5099467237/10000000000 : ℝ)|=(5099467237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_13 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135132773/250000000 : ℝ)*x 0 + (-25362519/200000000 : ℝ)*x 1 + (318716713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135132773/250000000 : ℝ)^5903 ≤ (47505657359627/100000000000000 : ℝ)^4879 := by
    have hnat : (135132773 : ℕ)^5903*100000000000000^4879 ≤ 47505657359627^4879*250000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135132773 250000000 47505657359627 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25362519/200000000 : ℝ)^5903 ≤ (4110597438387/50000000000000 : ℝ)^4879 := by
    have hnat : (25362519 : ℕ)^5903*50000000000000^4879 ≤ 4110597438387^4879*200000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25362519 200000000 4110597438387 50000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318716713/625000000 : ℝ)^5903 ≤ (44273147749127/100000000000000 : ℝ)^4879 := by
    have hnat : (318716713 : ℕ)^5903*100000000000000^4879 ≤ 44273147749127^4879*625000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318716713 625000000 44273147749127 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135132773/250000000 : ℝ), (-25362519/200000000 : ℝ), (318716713/625000000 : ℝ)] ![(47505657359627/100000000000000 : ℝ), (4110597438387/50000000000000 : ℝ), (44273147749127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135132773/250000000 : ℝ)|^5903 ≤ (47505657359627/100000000000000 : ℝ)^4879
        have hw : |(135132773/250000000 : ℝ)|=(135132773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25362519/200000000 : ℝ)|^5903 ≤ (4110597438387/50000000000000 : ℝ)^4879
        have hw : |(-25362519/200000000 : ℝ)|=(25362519/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318716713/625000000 : ℝ)|^5903 ≤ (44273147749127/100000000000000 : ℝ)^4879
        have hw : |(318716713/625000000 : ℝ)|=(318716713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_14 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405310889/10000000000 : ℝ)*x 0 + (2549733367/5000000000 : ℝ)*x 1 + (-253625379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405310889/10000000000 : ℝ)^5903 ≤ (11876414257499/25000000000000 : ℝ)^4879 := by
    have hnat : (5405310889 : ℕ)^5903*25000000000000^4879 ≤ 11876414257499^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405310889 10000000000 11876414257499 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549733367/5000000000 : ℝ)^5903 ≤ (8854628133877/20000000000000 : ℝ)^4879 := by
    have hnat : (2549733367 : ℕ)^5903*20000000000000^4879 ≤ 8854628133877^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549733367 5000000000 8854628133877 20000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253625379/2000000000 : ℝ)^5903 ≤ (25691257153/312500000000 : ℝ)^4879 := by
    have hnat : (253625379 : ℕ)^5903*312500000000^4879 ≤ 25691257153^4879*2000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253625379 2000000000 25691257153 312500000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405310889/10000000000 : ℝ), (2549733367/5000000000 : ℝ), (-253625379/2000000000 : ℝ)] ![(11876414257499/25000000000000 : ℝ), (8854628133877/20000000000000 : ℝ), (25691257153/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405310889/10000000000 : ℝ)|^5903 ≤ (11876414257499/25000000000000 : ℝ)^4879
        have hw : |(5405310889/10000000000 : ℝ)|=(5405310889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2549733367/5000000000 : ℝ)|^5903 ≤ (8854628133877/20000000000000 : ℝ)^4879
        have hw : |(2549733367/5000000000 : ℝ)|=(2549733367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253625379/2000000000 : ℝ)|^5903 ≤ (25691257153/312500000000 : ℝ)^4879
        have hw : |(-253625379/2000000000 : ℝ)|=(253625379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1758_box_15 (p : ℝ) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3323286907/10000000000 : ℝ)*x 0 + (2189089691/5000000000 : ℝ)*x 1 + (1094545603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3323286907/10000000000 : ℝ)^5903 ≤ (26372720814913/100000000000000 : ℝ)^4879 := by
    have hnat : (3323286907 : ℕ)^5903*100000000000000^4879 ≤ 26372720814913^4879*10000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3323286907 10000000000 26372720814913 100000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189089691/5000000000 : ℝ)^5903 ≤ (4601703021541/12500000000000 : ℝ)^4879 := by
    have hnat : (2189089691 : ℕ)^5903*12500000000000^4879 ≤ 4601703021541^4879*5000000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189089691 5000000000 4601703021541 12500000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094545603/2500000000 : ℝ)^5903 ≤ (9203413749271/25000000000000 : ℝ)^4879 := by
    have hnat : (1094545603 : ℕ)^5903*25000000000000^4879 ≤ 9203413749271^4879*2500000000^5903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094545603 2500000000 9203413749271 25000000000000 5903 4879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5903/1024 : ℝ)) 5903 4879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3323286907/10000000000 : ℝ), (2189089691/5000000000 : ℝ), (1094545603/2500000000 : ℝ)] ![(26372720814913/100000000000000 : ℝ), (4601703021541/12500000000000 : ℝ), (9203413749271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3323286907/10000000000 : ℝ)|^5903 ≤ (26372720814913/100000000000000 : ℝ)^4879
        have hw : |(3323286907/10000000000 : ℝ)|=(3323286907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2189089691/5000000000 : ℝ)|^5903 ≤ (4601703021541/12500000000000 : ℝ)^4879
        have hw : |(2189089691/5000000000 : ℝ)|=(2189089691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094545603/2500000000 : ℝ)|^5903 ≤ (9203413749271/25000000000000 : ℝ)^4879
        have hw : |(1094545603/2500000000 : ℝ)|=(1094545603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1758_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (891/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1827/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(17267/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11701/20000 : ℝ) ∧ (82019/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (18609/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (891/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1827/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (891/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1827/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (891/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1827/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (891/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1827/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (891/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1827/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (891/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1827/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1827/20000 : ℝ) ^ (5887/1024 : ℝ) ≤ (105947107715903/100000000000000000000 : ℝ) := by
    have hpowers : (1827/20000 : ℝ)^5887 ≤ (105947107715903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1827 : ℕ)^5887*100000000000000000000^1024 ≤ 105947107715903^1024*20000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1827 20000 105947107715903 100000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1827/20000 : ℝ)) (X := (105947107715903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (891/5000 : ℝ) ^ (5887/1024 : ℝ) ≤ (987371993416611/20000000000000000000 : ℝ) := by
    have hpowers : (891/5000 : ℝ)^5887 ≤ (987371993416611/20000000000000000000 : ℝ)^1024 := by
      have hnat : (891 : ℕ)^5887*20000000000000000000^1024 ≤ 987371993416611^1024*5000^5887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        891 5000 987371993416611 20000000000000000000 5887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (891/5000 : ℝ)) (X := (987371993416611/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000105947107715903/50000000000000000000 : ℝ) ≤ (500000184286977/500000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50000105947107715903/50000000000000000000 : ℝ)^1024 ≤ (500000184286977/500000000000000 : ℝ)^5887 := by
      have hnat : (50000105947107715903 : ℕ)^1024*500000000000000^5887 ≤ 500000184286977^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000105947107715903 50000000000000000000 500000184286977 500000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000184286977/500000000000000 : ℝ)) (X := (50000105947107715903/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50002521403537399479/50000000000000000000 : ℝ) ≤ (5000043857031547/5000000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (50002521403537399479/50000000000000000000 : ℝ)^1024 ≤ (5000043857031547/5000000000000000 : ℝ)^5887 := by
      have hnat : (50002521403537399479 : ℕ)^1024*5000000000000000^5887 ≤ 5000043857031547^5887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002521403537399479 50000000000000000000 5000043857031547 5000000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000043857031547/5000000000000000 : ℝ)) (X := (50002521403537399479/50000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10000987371993416611/10000000000000000000 : ℝ) ≤ (1250021467798331/1250000000000000 : ℝ) ^ (5887/1024 : ℝ) := by
    have hpowers : (10000987371993416611/10000000000000000000 : ℝ)^1024 ≤ (1250021467798331/1250000000000000 : ℝ)^5887 := by
      have hnat : (10000987371993416611 : ℕ)^1024*1250000000000000^5887 ≤ 1250021467798331^5887*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000987371993416611 10000000000000000000 1250021467798331 1250000000000000 1024 5887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250021467798331/1250000000000000 : ℝ)) (X := (10000987371993416611/10000000000000000000 : ℝ)) (by norm_num) 5887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(105947107715903/100000000000000000000 : ℝ) ≤ ((241245824481046037/241250000000000000 : ℝ)+2*(42014161777/434250000000000 : ℝ)*(1827/20000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (241245824481046037/241250000000000000 : ℝ)+2*(42014161777/434250000000000 : ℝ)*(1827/20000 : ℝ)=(500000184286977/500000000000000 : ℝ) by norm_num, show 1+2*(105947107715903/100000000000000000000 : ℝ)=(50000105947107715903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(987371993416611/20000000000000000000 : ℝ)+(105947107715903/100000000000000000000 : ℝ) ≤ ((241245824481046037/241250000000000000 : ℝ)+(42014161777/434250000000000 : ℝ)*((891/5000 : ℝ)+(1827/20000 : ℝ)))^(5887/1024 : ℝ) := by
    rw [show (241245824481046037/241250000000000000 : ℝ)+(42014161777/434250000000000 : ℝ)*((891/5000 : ℝ)+(1827/20000 : ℝ))=(5000043857031547/5000000000000000 : ℝ) by norm_num, show 1+(987371993416611/20000000000000000000 : ℝ)+(105947107715903/100000000000000000000 : ℝ)=(50002521403537399479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(987371993416611/20000000000000000000 : ℝ) ≤ ((241245824481046037/241250000000000000 : ℝ)+2*(42014161777/434250000000000 : ℝ)*(891/5000 : ℝ))^(5887/1024 : ℝ) := by
    rw [show (241245824481046037/241250000000000000 : ℝ)+2*(42014161777/434250000000000 : ℝ)*(891/5000 : ℝ)=(1250021467798331/1250000000000000 : ℝ) by norm_num, show 1+2*(987371993416611/20000000000000000000 : ℝ)=(10000987371993416611/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (241245824481046037/241250000000000000 : ℝ)*(X 1 0+X 2 0)+(42014161777/434250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (1827/20000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (241245824481046037/241250000000000000 : ℝ)) (alpha := (42014161777/434250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (241245824481046037/241250000000000000 : ℝ)*(X 0 1+X 2 1)+(42014161777/434250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (1827/20000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (241245824481046037/241250000000000000 : ℝ)) (alpha := (42014161777/434250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (241245824481046037/241250000000000000 : ℝ)*(X 0 2+X 1 2)+(42014161777/434250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5887/1024 : ℝ)) (lo := (1827/20000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (241245824481046037/241250000000000000 : ℝ)) (alpha := (42014161777/434250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-805086617/10000000000 : ℝ)*X 0 0+(5416784519/10000000000 : ℝ)*X 0 1+(5416784763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5193526961/10000000000 : ℝ)*X 1 0+(-140575423/1250000000 : ℝ)*X 1 1+(5416784611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((649190857/1250000000 : ℝ)*X 2 0+(2708392373/5000000000 : ℝ)*X 2 1+(-56230167/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1132420481/2500000000 : ℝ)*X 0 0+(945024109/2500000000 : ℝ)*X 0 1+(3780096421/10000000000 : ℝ)*X 0 2+(1132420481/2500000000 : ℝ)*X 1 0+(945024109/2500000000 : ℝ)*X 1 1+(3780096421/10000000000 : ℝ)*X 1 2+(1132420481/2500000000 : ℝ)*X 2 0+(945024109/2500000000 : ℝ)*X 2 1+(3780096421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398018271/2500000000 : ℝ)*X 0 0+(2564661853/5000000000 : ℝ)*X 0 1+(641165487/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385316659/10000000000 : ℝ)*X 1 0+(-627599473/5000000000 : ℝ)*X 1 1+(5129323891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385316851/10000000000 : ℝ)*X 2 0+(5129323831/10000000000 : ℝ)*X 2 1+(-1255198767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3441502343/10000000000 : ℝ)*X 0 0+(4322113917/10000000000 : ℝ)*X 0 1+(4322114347/10000000000 : ℝ)*X 0 2+(3441502343/10000000000 : ℝ)*X 1 0+(4322113917/10000000000 : ℝ)*X 1 1+(4322114347/10000000000 : ℝ)*X 1 2+(3441502343/10000000000 : ℝ)*X 2 0+(4322113917/10000000000 : ℝ)*X 2 1+(4322114347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1420726149/10000000000 : ℝ)*X 0 0+(490964681/1000000000 : ℝ)*X 0 1+(342377467/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((322045741/625000000 : ℝ)*X 1 0+(-1095419687/10000000000 : ℝ)*X 1 1+(5478039529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((515273191/1000000000 : ℝ)*X 2 0+(5478039787/10000000000 : ℝ)*X 2 1+(-4381677/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((190042241/400000000 : ℝ)*X 0 0+(1832084373/5000000000 : ℝ)*X 0 1+(732833331/2000000000 : ℝ)*X 0 2+(190042241/400000000 : ℝ)*X 1 0+(1832084373/5000000000 : ℝ)*X 1 1+(732833331/2000000000 : ℝ)*X 1 2+(190042241/400000000 : ℝ)*X 2 0+(1832084373/5000000000 : ℝ)*X 2 1+(732833331/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-481140951/5000000000 : ℝ)*X 0 0+(5623880003/10000000000 : ℝ)*X 0 1+(5099467237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((135132773/250000000 : ℝ)*X 1 0+(-25362519/200000000 : ℝ)*X 1 1+(318716713/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5405310889/10000000000 : ℝ)*X 2 0+(2549733367/5000000000 : ℝ)*X 2 1+(-253625379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3323286907/10000000000 : ℝ)*X 0 0+(2189089691/5000000000 : ℝ)*X 0 1+(1094545603/2500000000 : ℝ)*X 0 2+(3323286907/10000000000 : ℝ)*X 1 0+(2189089691/5000000000 : ℝ)*X 1 1+(1094545603/2500000000 : ℝ)*X 1 2+(3323286907/10000000000 : ℝ)*X 2 0+(2189089691/5000000000 : ℝ)*X 2 1+(1094545603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1758_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-17267/25000 : ℝ) ≤ (-64748748792498752986036019903/93750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2657009/25000000000000 : ℝ)*(upper0) + (480901/100000000000000 : ℝ)*(lower1) + (11981567/50000000000000 : ℝ)*(lower2) + (8051103/25000000000000 : ℝ)*(lower3) + (6703617/50000000000000 : ℝ)*(upper5) + (538505919865163/50000000000000 : ℝ)*(major0) + (538505919865163/50000000000000 : ℝ)*(major1) + (538505919865163/50000000000000 : ℝ)*(major2) + (337343619162541/20000000000000 : ℝ)*(sp4) + (1686707752949287/100000000000000 : ℝ)*(sp5) + (1686711965016299/100000000000000 : ℝ)*(sp6) + (98065472199277/20000000000000 : ℝ)*(sp7) + (10342863417/100000000000000 : ℝ)*(sp13) + (1226159281/20000000000000 : ℝ)*(sp14) + (98065472199277/20000000000000 : ℝ)*(f.failure) + (337343619162541/20000000000000 : ℝ)*(f.sum) + (350028499553/225000000000000000000000000 : ℝ)*base65 + (2107959553202597/562500000000000000000000000000 : ℝ)*base68 + (1643255521952597/562500000000000000000000000000 : ℝ)*base70 + (1611998604484903/562500000000000000000000000000 : ℝ)*base71 + (482847150997/225000000000000000000000000 : ℝ)*base74 + (4763265005734903/562500000000000000000000000000 : ℝ)*base75 + (1588923323922403/562500000000000000000000000000 : ℝ)*base77 + (1325580941734903/562500000000000000000000000000 : ℝ)*base79 + (1660018560353/225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2298847/2000000000000000000000 : ℝ)*base90 + (2298847/2000000000000000000000 : ℝ)*base92 + (2298847/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11701/20000 : ℝ) ≤ (3528718740679898425966893146821/6031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1363011/100000000000000 : ℝ)*(upper1) + (1110231/10000000000000 : ℝ)*(upper2) + (972643/50000000000000 : ℝ)*(upper3) + (7309067/100000000000000 : ℝ)*(upper4) + (1205313699322139/100000000000000 : ℝ)*(major0) + (1205313699322139/100000000000000 : ℝ)*(major1) + (1205313699322139/100000000000000 : ℝ)*(major2) + (368477037794887/20000000000000 : ℝ)*(sp0) + (14393641194061/781250000000 : ℝ)*(sp1) + (921192639629597/50000000000000 : ℝ)*(sp2) + (274369446815643/50000000000000 : ℝ)*(sp3) + (403921651/50000000000000 : ℝ)*(sp6) + (445709/3125000000000 : ℝ)*(sp9) + (898128061/100000000000000 : ℝ)*(sp12) + (274369446815643/50000000000000 : ℝ)*(f.failure) + (57574565221953/3125000000000 : ℝ)*(f.sum) + (256827391956031/43425000000000000000000000000 : ℝ)*base65 + (180517113047333287/217125000000000000000000000000000 : ℝ)*base67 + (30252255873833287/217125000000000000000000000000000 : ℝ)*base69 + (1008980557980833287/217125000000000000000000000000000 : ℝ)*base71 + (22541633481697/21712500000000000000000000000 : ℝ)*base74 + (270823004388083287/217125000000000000000000000000000 : ℝ)*base75 + (670234367974583287/217125000000000000000000000000000 : ℝ)*base77 + (148633256690916713/217125000000000000000000000000000 : ℝ)*base80 + (75397742675453/21712500000000000000000000000 : ℝ)*base81 + (25006727/5000000000000000000000 : ℝ)*base89 + (25006727/5000000000000000000000 : ℝ)*base91 + (25006727/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (82019/100000 : ℝ) ≤ (4946897468568306597215204858593/6031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63785169/100000000000000 : ℝ)*(upper1) + (1969289/2500000000000 : ℝ)*(upper4) + (237417/1250000000000 : ℝ)*(lower5) + (578316880898337/50000000000000 : ℝ)*(major0) + (578316880898337/50000000000000 : ℝ)*(major1) + (578316880898337/50000000000000 : ℝ)*(major2) + (21469858623/100000000000000 : ℝ)*(sp1) + (19225124119/50000000000000 : ℝ)*(sp2) + (1514542741/20000000000000 : ℝ)*(sp3) + (66185717/4000000000000 : ℝ)*(sp4) + (43983723796843/2500000000000 : ℝ)*(sp8) + (1759329136658023/100000000000000 : ℝ)*(sp9) + (1759312156268407/100000000000000 : ℝ)*(sp10) + (263284489194087/50000000000000 : ℝ)*(sp11) + (526576551101879/100000000000000 : ℝ)*(f.failure) + (879675303258323/50000000000000 : ℝ)*(f.sum) + (46976051028559/7237500000000000000000000000 : ℝ)*base66 + (110875950402261407/36187500000000000000000000000000 : ℝ)*base67 + (291074466152323907/36187500000000000000000000000000 : ℝ)*base69 + (104213637593551093/36187500000000000000000000000000 : ℝ)*base72 + (58835815182593/14475000000000000000000000000 : ℝ)*base74 + (117545019736426093/36187500000000000000000000000000 : ℝ)*base76 + (210815496259386407/36187500000000000000000000000000 : ℝ)*base77 + (204226180498948907/36187500000000000000000000000000 : ℝ)*base79 + (92550289716743/14475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (23235731/10000000000000000000000 : ℝ)*base89 + (23235731/10000000000000000000000 : ℝ)*base91 + (23235731/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-18609/20000 : ℝ) ≤ (-16834970252066453765953524214939/18093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59292877/100000000000000 : ℝ)*(upper3) + (202881203/100000000000000 : ℝ)*(lower4) + (679553/390625000000 : ℝ)*(upper5) + (1214373471975433/100000000000000 : ℝ)*(major0) + (1214373471975433/100000000000000 : ℝ)*(major1) + (1214373471975433/100000000000000 : ℝ)*(major2) + (980748829/50000000000000 : ℝ)*(sp4) + (10899241503/100000000000000 : ℝ)*(sp5) + (109413640099/100000000000000 : ℝ)*(sp6) + (2409588101/12500000000000 : ℝ)*(sp7) + (476723954020319/25000000000000 : ℝ)*(sp12) + (190688687833743/10000000000000 : ℝ)*(sp13) + (953394181969417/50000000000000 : ℝ)*(sp14) + (13821105687369/2500000000000 : ℝ)*(sp15) + (34553969012473/6250000000000 : ℝ)*(f.failure) + (953448888789467/50000000000000 : ℝ)*(f.sum) + (10069013713441/21712500000000000000000000000 : ℝ)*base65 + (881722904521713811/217125000000000000000000000000000 : ℝ)*base68 + (132842327849786189/217125000000000000000000000000000 : ℝ)*base69 + (874025641861661189/217125000000000000000000000000000 : ℝ)*base71 + (64603111541317/10856250000000000000000000000 : ℝ)*base74 + (825571035034661189/217125000000000000000000000000000 : ℝ)*base75 + (797958590895911189/217125000000000000000000000000000 : ℝ)*base77 + (184438348464161189/217125000000000000000000000000000 : ℝ)*base79 + (3058517301643/43425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (980403/625000000000000000000 : ℝ)*base90 + (980403/625000000000000000000 : ℝ)*base92 + (980403/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1758_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (891/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1827/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17267/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11701/20000 : ℝ) else (82019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18609/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1758_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1758_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17267/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11701/20000 : ℝ) else (82019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18609/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1758_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1758_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5887/1024 : ℝ) ≤ p) (hpb : p ≤ (5903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (219651589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17267/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11701/20000 : ℝ) else (82019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (18609/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1758_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
