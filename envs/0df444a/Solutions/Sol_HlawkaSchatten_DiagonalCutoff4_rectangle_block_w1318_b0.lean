-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:20.289013+00:00
-- url     : https://prove2.me/submissions/53db7c01-9270-45c0-8fd6-1d394a208a8a

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
theorem support_rectangle_w1318_s0_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823419659/10000000000 : ℝ)*x 0 + (3003673557/5000000000 : ℝ)*x 1 + (600643827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823419659/10000000000 : ℝ)^2139 ≤ (10673216857053/100000000000000 : ℝ)^1627 := by
    have hnat : (1823419659 : ℕ)^2139*100000000000000^1627 ≤ 10673216857053^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823419659 10000000000 10673216857053 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3003673557/5000000000 : ℝ)^2139 ≤ (25586240882691/50000000000000 : ℝ)^1627 := by
    have hnat : (3003673557 : ℕ)^2139*50000000000000^1627 ≤ 25586240882691^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003673557 5000000000 25586240882691 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600643827/1250000000 : ℝ)^2139 ≤ (38154301366891/100000000000000 : ℝ)^1627 := by
    have hnat : (600643827 : ℕ)^2139*100000000000000^1627 ≤ 38154301366891^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600643827 1250000000 38154301366891 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823419659/10000000000 : ℝ), (3003673557/5000000000 : ℝ), (600643827/1250000000 : ℝ)] ![(10673216857053/100000000000000 : ℝ), (25586240882691/50000000000000 : ℝ), (38154301366891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823419659/10000000000 : ℝ)|^2139 ≤ (10673216857053/100000000000000 : ℝ)^1627
        have hw : |(-1823419659/10000000000 : ℝ)|=(1823419659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3003673557/5000000000 : ℝ)|^2139 ≤ (25586240882691/50000000000000 : ℝ)^1627
        have hw : |(3003673557/5000000000 : ℝ)|=(3003673557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600643827/1250000000 : ℝ)|^2139 ≤ (38154301366891/100000000000000 : ℝ)^1627
        have hw : |(600643827/1250000000 : ℝ)|=(600643827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5504502333/10000000000 : ℝ)*x 0 + (-626985871/2500000000 : ℝ)*x 1 + (2402575343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504502333/10000000000 : ℝ)^2139 ≤ (2851049412063/6250000000000 : ℝ)^1627 := by
    have hnat : (5504502333 : ℕ)^2139*6250000000000^1627 ≤ 2851049412063^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504502333 10000000000 2851049412063 6250000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626985871/2500000000 : ℝ)^2139 ≤ (3245781459307/20000000000000 : ℝ)^1627 := by
    have hnat : (626985871 : ℕ)^2139*20000000000000^1627 ≤ 3245781459307^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626985871 2500000000 3245781459307 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2402575343/5000000000 : ℝ)^2139 ≤ (19077151048811/50000000000000 : ℝ)^1627 := by
    have hnat : (2402575343 : ℕ)^2139*50000000000000^1627 ≤ 19077151048811^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402575343 5000000000 19077151048811 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504502333/10000000000 : ℝ), (-626985871/2500000000 : ℝ), (2402575343/5000000000 : ℝ)] ![(2851049412063/6250000000000 : ℝ), (3245781459307/20000000000000 : ℝ), (19077151048811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504502333/10000000000 : ℝ)|^2139 ≤ (2851049412063/6250000000000 : ℝ)^1627
        have hw : |(5504502333/10000000000 : ℝ)|=(5504502333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-626985871/2500000000 : ℝ)|^2139 ≤ (3245781459307/20000000000000 : ℝ)^1627
        have hw : |(-626985871/2500000000 : ℝ)|=(626985871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2402575343/5000000000 : ℝ)|^2139 ≤ (19077151048811/50000000000000 : ℝ)^1627
        have hw : |(2402575343/5000000000 : ℝ)|=(2402575343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1376125391/2500000000 : ℝ)*x 0 + (2402575583/5000000000 : ℝ)*x 1 + (-62698597/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376125391/2500000000 : ℝ)^2139 ≤ (22808391107351/50000000000000 : ℝ)^1627 := by
    have hnat : (1376125391 : ℕ)^2139*50000000000000^1627 ≤ 22808391107351^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376125391 2500000000 22808391107351 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2402575583/5000000000 : ℝ)^2139 ≤ (74520131071/195312500000 : ℝ)^1627 := by
    have hnat : (2402575583 : ℕ)^2139*195312500000^1627 ≤ 74520131071^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402575583 5000000000 74520131071 195312500000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62698597/250000000 : ℝ)^2139 ≤ (16228910665449/100000000000000 : ℝ)^1627 := by
    have hnat : (62698597 : ℕ)^2139*100000000000000^1627 ≤ 16228910665449^1627*250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62698597 250000000 16228910665449 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376125391/2500000000 : ℝ), (2402575583/5000000000 : ℝ), (-62698597/250000000 : ℝ)] ![(22808391107351/50000000000000 : ℝ), (74520131071/195312500000 : ℝ), (16228910665449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376125391/2500000000 : ℝ)|^2139 ≤ (22808391107351/50000000000000 : ℝ)^1627
        have hw : |(1376125391/2500000000 : ℝ)|=(1376125391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2402575583/5000000000 : ℝ)|^2139 ≤ (74520131071/195312500000 : ℝ)^1627
        have hw : |(2402575583/5000000000 : ℝ)|=(2402575583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62698597/250000000 : ℝ)|^2139 ≤ (16228910665449/100000000000000 : ℝ)^1627
        have hw : |(-62698597/250000000 : ℝ)|=(62698597/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (52279527/125000000 : ℝ)*x 0 + (3107844339/10000000000 : ℝ)*x 1 + (5603211523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52279527/125000000 : ℝ)^2139 ≤ (31789738690163/100000000000000 : ℝ)^1627 := by
    have hnat : (52279527 : ℕ)^2139*100000000000000^1627 ≤ 31789738690163^1627*125000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52279527 125000000 31789738690163 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107844339/10000000000 : ℝ)^2139 ≤ (21515005376151/100000000000000 : ℝ)^1627 := by
    have hnat : (3107844339 : ℕ)^2139*100000000000000^1627 ≤ 21515005376151^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107844339 10000000000 21515005376151 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5603211523/10000000000 : ℝ)^2139 ≤ (9339051184621/20000000000000 : ℝ)^1627 := by
    have hnat : (5603211523 : ℕ)^2139*20000000000000^1627 ≤ 9339051184621^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603211523 10000000000 9339051184621 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52279527/125000000 : ℝ), (3107844339/10000000000 : ℝ), (5603211523/10000000000 : ℝ)] ![(31789738690163/100000000000000 : ℝ), (21515005376151/100000000000000 : ℝ), (9339051184621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52279527/125000000 : ℝ)|^2139 ≤ (31789738690163/100000000000000 : ℝ)^1627
        have hw : |(52279527/125000000 : ℝ)|=(52279527/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107844339/10000000000 : ℝ)|^2139 ≤ (21515005376151/100000000000000 : ℝ)^1627
        have hw : |(3107844339/10000000000 : ℝ)|=(3107844339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5603211523/10000000000 : ℝ)|^2139 ≤ (9339051184621/20000000000000 : ℝ)^1627
        have hw : |(5603211523/10000000000 : ℝ)|=(5603211523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-914001797/5000000000 : ℝ)*x 0 + (2418067283/5000000000 : ℝ)*x 1 + (1195051649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914001797/5000000000 : ℝ)^2139 ≤ (2677126518809/25000000000000 : ℝ)^1627 := by
    have hnat : (914001797 : ℕ)^2139*25000000000000^1627 ≤ 2677126518809^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914001797 5000000000 2677126518809 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418067283/5000000000 : ℝ)^2139 ≤ (384780711153/1000000000000 : ℝ)^1627 := by
    have hnat : (2418067283 : ℕ)^2139*1000000000000^1627 ≤ 384780711153^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418067283 5000000000 384780711153 1000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195051649/2000000000 : ℝ)^2139 ≤ (25406711397323/50000000000000 : ℝ)^1627 := by
    have hnat : (1195051649 : ℕ)^2139*50000000000000^1627 ≤ 25406711397323^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195051649 2000000000 25406711397323 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914001797/5000000000 : ℝ), (2418067283/5000000000 : ℝ), (1195051649/2000000000 : ℝ)] ![(2677126518809/25000000000000 : ℝ), (384780711153/1000000000000 : ℝ), (25406711397323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914001797/5000000000 : ℝ)|^2139 ≤ (2677126518809/25000000000000 : ℝ)^1627
        have hw : |(-914001797/5000000000 : ℝ)|=(914001797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418067283/5000000000 : ℝ)|^2139 ≤ (384780711153/1000000000000 : ℝ)^1627
        have hw : |(2418067283/5000000000 : ℝ)|=(2418067283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195051649/2000000000 : ℝ)|^2139 ≤ (25406711397323/50000000000000 : ℝ)^1627
        have hw : |(1195051649/2000000000 : ℝ)|=(1195051649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5177025151/10000000000 : ℝ)*x 0 + (-1337836847/10000000000 : ℝ)*x 1 + (2987629073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177025151/10000000000 : ℝ)^2139 ≤ (1052069222823/2500000000000 : ℝ)^1627 := by
    have hnat : (5177025151 : ℕ)^2139*2500000000000^1627 ≤ 1052069222823^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177025151 10000000000 1052069222823 2500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1337836847/10000000000 : ℝ)^2139 ≤ (3551904693947/50000000000000 : ℝ)^1627 := by
    have hnat : (1337836847 : ℕ)^2139*50000000000000^1627 ≤ 3551904693947^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337836847 10000000000 3551904693947 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2987629073/5000000000 : ℝ)^2139 ≤ (50813421687817/100000000000000 : ℝ)^1627 := by
    have hnat : (2987629073 : ℕ)^2139*100000000000000^1627 ≤ 50813421687817^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987629073 5000000000 50813421687817 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177025151/10000000000 : ℝ), (-1337836847/10000000000 : ℝ), (2987629073/5000000000 : ℝ)] ![(1052069222823/2500000000000 : ℝ), (3551904693947/50000000000000 : ℝ), (50813421687817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177025151/10000000000 : ℝ)|^2139 ≤ (1052069222823/2500000000000 : ℝ)^1627
        have hw : |(5177025151/10000000000 : ℝ)|=(5177025151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1337836847/10000000000 : ℝ)|^2139 ≤ (3551904693947/50000000000000 : ℝ)^1627
        have hw : |(-1337836847/10000000000 : ℝ)|=(1337836847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2987629073/5000000000 : ℝ)|^2139 ≤ (50813421687817/100000000000000 : ℝ)^1627
        have hw : |(2987629073/5000000000 : ℝ)|=(2987629073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5177025181/10000000000 : ℝ)*x 0 + (5975258203/10000000000 : ℝ)*x 1 + (-1337836709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177025181/10000000000 : ℝ)^2139 ≤ (10520692308381/25000000000000 : ℝ)^1627 := by
    have hnat : (5177025181 : ℕ)^2139*25000000000000^1627 ≤ 10520692308381^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177025181 10000000000 10520692308381 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5975258203/10000000000 : ℝ)^2139 ≤ (25406711162541/50000000000000 : ℝ)^1627 := by
    have hnat : (5975258203 : ℕ)^2139*50000000000000^1627 ≤ 25406711162541^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5975258203 10000000000 25406711162541 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1337836709/10000000000 : ℝ)^2139 ≤ (710380842453/10000000000000 : ℝ)^1627 := by
    have hnat : (1337836709 : ℕ)^2139*10000000000000^1627 ≤ 710380842453^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337836709 10000000000 710380842453 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177025181/10000000000 : ℝ), (5975258203/10000000000 : ℝ), (-1337836709/10000000000 : ℝ)] ![(10520692308381/25000000000000 : ℝ), (25406711162541/50000000000000 : ℝ), (710380842453/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177025181/10000000000 : ℝ)|^2139 ≤ (10520692308381/25000000000000 : ℝ)^1627
        have hw : |(5177025181/10000000000 : ℝ)|=(5177025181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5975258203/10000000000 : ℝ)|^2139 ≤ (25406711162541/50000000000000 : ℝ)^1627
        have hw : |(5975258203/10000000000 : ℝ)|=(5975258203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1337836709/10000000000 : ℝ)|^2139 ≤ (710380842453/10000000000000 : ℝ)^1627
        have hw : |(-1337836709/10000000000 : ℝ)|=(1337836709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s0_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2095938059/5000000000 : ℝ)*x 0 + (1107779913/2000000000 : ℝ)*x 1 + (1587224819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095938059/5000000000 : ℝ)^2139 ≤ (7971211019409/25000000000000 : ℝ)^1627 := by
    have hnat : (2095938059 : ℕ)^2139*25000000000000^1627 ≤ 7971211019409^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095938059 5000000000 7971211019409 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107779913/2000000000 : ℝ)^2139 ≤ (5748989835923/12500000000000 : ℝ)^1627 := by
    have hnat : (1107779913 : ℕ)^2139*12500000000000^1627 ≤ 5748989835923^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107779913 2000000000 5748989835923 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587224819/5000000000 : ℝ)^2139 ≤ (4424647445267/20000000000000 : ℝ)^1627 := by
    have hnat : (1587224819 : ℕ)^2139*20000000000000^1627 ≤ 4424647445267^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587224819 5000000000 4424647445267 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095938059/5000000000 : ℝ), (1107779913/2000000000 : ℝ), (1587224819/5000000000 : ℝ)] ![(7971211019409/25000000000000 : ℝ), (5748989835923/12500000000000 : ℝ), (4424647445267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095938059/5000000000 : ℝ)|^2139 ≤ (7971211019409/25000000000000 : ℝ)^1627
        have hw : |(2095938059/5000000000 : ℝ)|=(2095938059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107779913/2000000000 : ℝ)|^2139 ≤ (5748989835923/12500000000000 : ℝ)^1627
        have hw : |(1107779913/2000000000 : ℝ)|=(1107779913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587224819/5000000000 : ℝ)|^2139 ≤ (4424647445267/20000000000000 : ℝ)^1627
        have hw : |(1587224819/5000000000 : ℝ)|=(1587224819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1233/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5409/20000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4277/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4277 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4277*1^1024 ≤ 0^1024*1^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4277/1024 : ℝ) ≤ (1088606602959753609/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4277 ≤ (1088606602959753609/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4277*50000000000000000000^1024 ≤ 1088606602959753609^1024*5^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1088606602959753609 50000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1088606602959753609/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4277 := by
      have hnat : (1 : ℕ)^1024*1^4277 ≤ 1^4277*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51088606602959753609/50000000000000000000 : ℝ) ≤ (2512925177299711/2500000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (51088606602959753609/50000000000000000000 : ℝ)^1024 ≤ (2512925177299711/2500000000000000 : ℝ)^4277 := by
      have hnat : (51088606602959753609 : ℕ)^1024*2500000000000000^4277 ≤ 2512925177299711^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51088606602959753609 50000000000000000000 2512925177299711 2500000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512925177299711/2500000000000000 : ℝ)) (X := (51088606602959753609/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26088606602959753609/25000000000000000000 : ℝ) ≤ (1262925177299711/1250000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (26088606602959753609/25000000000000000000 : ℝ)^1024 ≤ (1262925177299711/1250000000000000 : ℝ)^4277 := by
      have hnat : (26088606602959753609 : ℕ)^1024*1250000000000000^4277 ≤ 1262925177299711^4277*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26088606602959753609 25000000000000000000 1262925177299711 1250000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262925177299711/1250000000000000 : ℝ)) (X := (26088606602959753609/25000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12925177299711/1000000000000000 : ℝ)*(0 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12925177299711/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1088606602959753609/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12925177299711/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12925177299711/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512925177299711/2500000000000000 : ℝ) by norm_num, show 1+(1088606602959753609/50000000000000000000 : ℝ)+(0 : ℝ)=(51088606602959753609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1088606602959753609/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12925177299711/1000000000000000 : ℝ)*(2/5 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12925177299711/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262925177299711/1250000000000000 : ℝ) by norm_num, show 1+2*(1088606602959753609/50000000000000000000 : ℝ)=(26088606602959753609/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12925177299711/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12925177299711/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12925177299711/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12925177299711/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12925177299711/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12925177299711/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1823419659/10000000000 : ℝ)*X 0 0+(3003673557/5000000000 : ℝ)*X 0 1+(600643827/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5504502333/10000000000 : ℝ)*X 1 0+(-626985871/2500000000 : ℝ)*X 1 1+(2402575343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1376125391/2500000000 : ℝ)*X 2 0+(2402575583/5000000000 : ℝ)*X 2 1+(-62698597/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52279527/125000000 : ℝ)*X 0 0+(3107844339/10000000000 : ℝ)*X 0 1+(5603211523/10000000000 : ℝ)*X 0 2+(52279527/125000000 : ℝ)*X 1 0+(3107844339/10000000000 : ℝ)*X 1 1+(5603211523/10000000000 : ℝ)*X 1 2+(52279527/125000000 : ℝ)*X 2 0+(3107844339/10000000000 : ℝ)*X 2 1+(5603211523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-914001797/5000000000 : ℝ)*X 0 0+(2418067283/5000000000 : ℝ)*X 0 1+(1195051649/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5177025151/10000000000 : ℝ)*X 1 0+(-1337836847/10000000000 : ℝ)*X 1 1+(2987629073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177025181/10000000000 : ℝ)*X 2 0+(5975258203/10000000000 : ℝ)*X 2 1+(-1337836709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2095938059/5000000000 : ℝ)*X 0 0+(1107779913/2000000000 : ℝ)*X 0 1+(1587224819/5000000000 : ℝ)*X 0 2+(2095938059/5000000000 : ℝ)*X 1 0+(1107779913/2000000000 : ℝ)*X 1 1+(1587224819/5000000000 : ℝ)*X 1 2+(2095938059/5000000000 : ℝ)*X 2 0+(1107779913/2000000000 : ℝ)*X 2 1+(1587224819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2882335830977422124649/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (11404639/25000000000000 : ℝ)*(base1) + (3326061/20000000000000 : ℝ)*(base16) + (131613941/25000000000000 : ℝ)*(base19) + (426878513/100000000000000 : ℝ)*(base23) + (82107379/100000000000000 : ℝ)*(upper3) + (77034894789631/12500000000000 : ℝ)*(major0) + (77034894789631/12500000000000 : ℝ)*(major1) + (77034894789631/12500000000000 : ℝ)*(major2) + (166362556076173/20000000000000 : ℝ)*(sp0) + (207953405342679/25000000000000 : ℝ)*(sp1) + (25994179299321/3125000000000 : ℝ)*(sp2) + (400743241379207/100000000000000 : ℝ)*(sp3) + (57187779/4000000000000 : ℝ)*(sp4) + (803689711/100000000000000 : ℝ)*(sp7) + (200372045343737/50000000000000 : ℝ)*(f.failure) + (51988385278549/6250000000000 : ℝ)*(f.sum) + (1164101890391/6250000000000000000000000000 : ℝ)*base65 + (39025909753359/12500000000000000000000000000 : ℝ)*base68 + (73299719078359/12500000000000000000000000000 : ℝ)*base70 + (89591885978359/12500000000000000000000000000 : ℝ)*base72 + (5419979946641/6250000000000000000000000000 : ℝ)*base73 + (129595368590859/12500000000000000000000000000 : ℝ)*base76 + (76048598228359/12500000000000000000000000000 : ℝ)*base78 + (128673018403359/12500000000000000000000000000 : ℝ)*base80 + (10832402397109/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (18530429/5000000000000000000000 : ℝ)*base89 + (18530429/5000000000000000000000 : ℝ)*base91 + (18530429/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166885306941289107099573/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1590046547/100000000000000 : ℝ)*(base19) + (1611515801/100000000000000 : ℝ)*(base23) + (11393933/20000000000000 : ℝ)*(base32) + (109117467/50000000000000 : ℝ)*(upper3) + (10308617/6250000000000 : ℝ)*(upper5) + (325199757360227/50000000000000 : ℝ)*(major0) + (325199757360227/50000000000000 : ℝ)*(major1) + (325199757360227/50000000000000 : ℝ)*(major2) + (3529819959/100000000000000 : ℝ)*(sp1) + (18944059/500000000000 : ℝ)*(sp2) + (877867480120659/100000000000000 : ℝ)*(sp4) + (877862360254153/100000000000000 : ℝ)*(sp5) + (438931039896529/50000000000000 : ℝ)*(sp6) + (105732817459209/25000000000000 : ℝ)*(sp7) + (845862653613/200000000000 : ℝ)*(f.failure) + (877867480120659/100000000000000 : ℝ)*(f.sum) + (28272485055603/25000000000000000000000000000 : ℝ)*base66 + (37885396705603/50000000000000000000000000000 : ℝ)*base68 + (49020928844397/50000000000000000000000000000 : ℝ)*base69 + (8974084905603/50000000000000000000000000000 : ℝ)*base72 + (31436719830603/25000000000000000000000000000 : ℝ)*base74 + (23803990994397/50000000000000000000000000000 : ℝ)*base75 + (35126802694397/50000000000000000000000000000 : ℝ)*base77 + (139931125705603/50000000000000000000000000000 : ℝ)*base80 + (17829511155603/25000000000000000000000000000 : ℝ)*base82 + (180479/20000000000000000000 : ℝ)*base90 + (180479/20000000000000000000 : ℝ)*base92 + (180479/20000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1318_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5409/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1318_s1_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-402340011/2000000000 : ℝ)*x 0 + (1413268283/2500000000 : ℝ)*x 1 + (5038869683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402340011/2000000000 : ℝ)^2139 ≤ (12145119983267/100000000000000 : ℝ)^1627 := by
    have hnat : (402340011 : ℕ)^2139*100000000000000^1627 ≤ 12145119983267^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402340011 2000000000 12145119983267 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413268283/2500000000 : ℝ)^2139 ≤ (11810577952277/25000000000000 : ℝ)^1627 := by
    have hnat : (1413268283 : ℕ)^2139*25000000000000^1627 ≤ 11810577952277^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413268283 2500000000 11810577952277 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038869683/10000000000 : ℝ)^2139 ≤ (5076571023227/12500000000000 : ℝ)^1627 := by
    have hnat : (5038869683 : ℕ)^2139*12500000000000^1627 ≤ 5076571023227^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038869683 10000000000 5076571023227 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402340011/2000000000 : ℝ), (1413268283/2500000000 : ℝ), (5038869683/10000000000 : ℝ)] ![(12145119983267/100000000000000 : ℝ), (11810577952277/25000000000000 : ℝ), (5076571023227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402340011/2000000000 : ℝ)|^2139 ≤ (12145119983267/100000000000000 : ℝ)^1627
        have hw : |(-402340011/2000000000 : ℝ)|=(402340011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1413268283/2500000000 : ℝ)|^2139 ≤ (11810577952277/25000000000000 : ℝ)^1627
        have hw : |(1413268283/2500000000 : ℝ)|=(1413268283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038869683/10000000000 : ℝ)|^2139 ≤ (5076571023227/12500000000000 : ℝ)^1627
        have hw : |(5038869683/10000000000 : ℝ)|=(5038869683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081646997/2000000000 : ℝ)*x 0 + (-1170068429/5000000000 : ℝ)*x 1 + (5038869729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081646997/2000000000 : ℝ)^2139 ≤ (557135614901/1250000000000 : ℝ)^1627 := by
    have hnat : (1081646997 : ℕ)^2139*1250000000000^1627 ≤ 557135614901^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081646997 2000000000 557135614901 1250000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170068429/5000000000 : ℝ)^2139 ≤ (231509095589/1562500000000 : ℝ)^1627 := by
    have hnat : (1170068429 : ℕ)^2139*1562500000000^1627 ≤ 231509095589^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170068429 5000000000 231509095589 1562500000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038869729/10000000000 : ℝ)^2139 ≤ (40612568673241/100000000000000 : ℝ)^1627 := by
    have hnat : (5038869729 : ℕ)^2139*100000000000000^1627 ≤ 40612568673241^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038869729 10000000000 40612568673241 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081646997/2000000000 : ℝ), (-1170068429/5000000000 : ℝ), (5038869729/10000000000 : ℝ)] ![(557135614901/1250000000000 : ℝ), (231509095589/1562500000000 : ℝ), (40612568673241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081646997/2000000000 : ℝ)|^2139 ≤ (557135614901/1250000000000 : ℝ)^1627
        have hw : |(1081646997/2000000000 : ℝ)|=(1081646997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1170068429/5000000000 : ℝ)|^2139 ≤ (231509095589/1562500000000 : ℝ)^1627
        have hw : |(-1170068429/5000000000 : ℝ)|=(1170068429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038869729/10000000000 : ℝ)|^2139 ≤ (40612568673241/100000000000000 : ℝ)^1627
        have hw : |(5038869729/10000000000 : ℝ)|=(5038869729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2704117489/5000000000 : ℝ)*x 0 + (1259717403/2500000000 : ℝ)*x 1 + (-2340137017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704117489/5000000000 : ℝ)^2139 ≤ (44570849116237/100000000000000 : ℝ)^1627 := by
    have hnat : (2704117489 : ℕ)^2139*100000000000000^1627 ≤ 44570849116237^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704117489 5000000000 44570849116237 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259717403/2500000000 : ℝ)^2139 ≤ (8122513486697/20000000000000 : ℝ)^1627 := by
    have hnat : (1259717403 : ℕ)^2139*20000000000000^1627 ≤ 8122513486697^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259717403 2500000000 8122513486697 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2340137017/10000000000 : ℝ)^2139 ≤ (7408291720603/50000000000000 : ℝ)^1627 := by
    have hnat : (2340137017 : ℕ)^2139*50000000000000^1627 ≤ 7408291720603^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340137017 10000000000 7408291720603 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704117489/5000000000 : ℝ), (1259717403/2500000000 : ℝ), (-2340137017/10000000000 : ℝ)] ![(44570849116237/100000000000000 : ℝ), (8122513486697/20000000000000 : ℝ), (7408291720603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704117489/5000000000 : ℝ)|^2139 ≤ (44570849116237/100000000000000 : ℝ)^1627
        have hw : |(2704117489/5000000000 : ℝ)|=(2704117489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1259717403/2500000000 : ℝ)|^2139 ≤ (8122513486697/20000000000000 : ℝ)^1627
        have hw : |(1259717403/2500000000 : ℝ)|=(1259717403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2340137017/10000000000 : ℝ)|^2139 ≤ (7408291720603/50000000000000 : ℝ)^1627
        have hw : |(-2340137017/10000000000 : ℝ)|=(2340137017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33566927/78125000 : ℝ)*x 0 + (231463017/625000000 : ℝ)*x 1 + (4978294379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33566927/78125000 : ℝ)^2139 ≤ (514622468377/1562500000000 : ℝ)^1627 := by
    have hnat : (33566927 : ℕ)^2139*1562500000000^1627 ≤ 514622468377^1627*78125000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33566927 78125000 514622468377 1562500000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231463017/625000000 : ℝ)^2139 ≤ (27092245002969/100000000000000 : ℝ)^1627 := by
    have hnat : (231463017 : ℕ)^2139*100000000000000^1627 ≤ 27092245002969^1627*625000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231463017 625000000 27092245002969 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4978294379/10000000000 : ℝ)^2139 ≤ (39971917010793/100000000000000 : ℝ)^1627 := by
    have hnat : (4978294379 : ℕ)^2139*100000000000000^1627 ≤ 39971917010793^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978294379 10000000000 39971917010793 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33566927/78125000 : ℝ), (231463017/625000000 : ℝ), (4978294379/10000000000 : ℝ)] ![(514622468377/1562500000000 : ℝ), (27092245002969/100000000000000 : ℝ), (39971917010793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33566927/78125000 : ℝ)|^2139 ≤ (514622468377/1562500000000 : ℝ)^1627
        have hw : |(33566927/78125000 : ℝ)|=(33566927/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231463017/625000000 : ℝ)|^2139 ≤ (27092245002969/100000000000000 : ℝ)^1627
        have hw : |(231463017/625000000 : ℝ)|=(231463017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4978294379/10000000000 : ℝ)|^2139 ≤ (39971917010793/100000000000000 : ℝ)^1627
        have hw : |(4978294379/10000000000 : ℝ)|=(4978294379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-201228267/1000000000 : ℝ)*x 0 + (630839949/1250000000 : ℝ)*x 1 + (141126943/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201228267/1000000000 : ℝ)^2139 ≤ (12149744467083/100000000000000 : ℝ)^1627 := by
    have hnat : (201228267 : ℕ)^2139*100000000000000^1627 ≤ 12149744467083^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201228267 1000000000 12149744467083 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630839949/1250000000 : ℝ)^2139 ≤ (20347883926149/50000000000000 : ℝ)^1627 := by
    have hnat : (630839949 : ℕ)^2139*50000000000000^1627 ≤ 20347883926149^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630839949 1250000000 20347883926149 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141126943/250000000 : ℝ)^2139 ≤ (47154487664777/100000000000000 : ℝ)^1627 := by
    have hnat : (141126943 : ℕ)^2139*100000000000000^1627 ≤ 47154487664777^1627*250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141126943 250000000 47154487664777 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201228267/1000000000 : ℝ), (630839949/1250000000 : ℝ), (141126943/250000000 : ℝ)] ![(12149744467083/100000000000000 : ℝ), (20347883926149/50000000000000 : ℝ), (47154487664777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201228267/1000000000 : ℝ)|^2139 ≤ (12149744467083/100000000000000 : ℝ)^1627
        have hw : |(-201228267/1000000000 : ℝ)|=(201228267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(630839949/1250000000 : ℝ)|^2139 ≤ (20347883926149/50000000000000 : ℝ)^1627
        have hw : |(630839949/1250000000 : ℝ)|=(630839949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141126943/250000000 : ℝ)|^2139 ≤ (47154487664777/100000000000000 : ℝ)^1627
        have hw : |(141126943/250000000 : ℝ)|=(141126943/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049836513/2000000000 : ℝ)*x 0 + (-1733929279/10000000000 : ℝ)*x 1 + (5645077371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049836513/2000000000 : ℝ)^2139 ≤ (10713896454207/25000000000000 : ℝ)^1627 := by
    have hnat : (1049836513 : ℕ)^2139*25000000000000^1627 ≤ 10713896454207^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049836513 2000000000 10713896454207 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1733929279/10000000000 : ℝ)^2139 ≤ (4994965168911/50000000000000 : ℝ)^1627 := by
    have hnat : (1733929279 : ℕ)^2139*50000000000000^1627 ≤ 4994965168911^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733929279 10000000000 4994965168911 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5645077371/10000000000 : ℝ)^2139 ≤ (5894310479013/12500000000000 : ℝ)^1627 := by
    have hnat : (5645077371 : ℕ)^2139*12500000000000^1627 ≤ 5894310479013^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5645077371 10000000000 5894310479013 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049836513/2000000000 : ℝ), (-1733929279/10000000000 : ℝ), (5645077371/10000000000 : ℝ)] ![(10713896454207/25000000000000 : ℝ), (4994965168911/50000000000000 : ℝ), (5894310479013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049836513/2000000000 : ℝ)|^2139 ≤ (10713896454207/25000000000000 : ℝ)^1627
        have hw : |(1049836513/2000000000 : ℝ)|=(1049836513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1733929279/10000000000 : ℝ)|^2139 ≤ (4994965168911/50000000000000 : ℝ)^1627
        have hw : |(-1733929279/10000000000 : ℝ)|=(1733929279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5645077371/10000000000 : ℝ)|^2139 ≤ (5894310479013/12500000000000 : ℝ)^1627
        have hw : |(5645077371/10000000000 : ℝ)|=(5645077371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624591209/5000000000 : ℝ)*x 0 + (2822538607/5000000000 : ℝ)*x 1 + (-346785943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624591209/5000000000 : ℝ)^2139 ≤ (42855584239013/100000000000000 : ℝ)^1627 := by
    have hnat : (2624591209 : ℕ)^2139*100000000000000^1627 ≤ 42855584239013^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624591209 5000000000 42855584239013 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2822538607/5000000000 : ℝ)^2139 ≤ (943089642159/2000000000000 : ℝ)^1627 := by
    have hnat : (2822538607 : ℕ)^2139*2000000000000^1627 ≤ 943089642159^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822538607 5000000000 943089642159 2000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346785943/2000000000 : ℝ)^2139 ≤ (9989933640307/100000000000000 : ℝ)^1627 := by
    have hnat : (346785943 : ℕ)^2139*100000000000000^1627 ≤ 9989933640307^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346785943 2000000000 9989933640307 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624591209/5000000000 : ℝ), (2822538607/5000000000 : ℝ), (-346785943/2000000000 : ℝ)] ![(42855584239013/100000000000000 : ℝ), (943089642159/2000000000000 : ℝ), (9989933640307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624591209/5000000000 : ℝ)|^2139 ≤ (42855584239013/100000000000000 : ℝ)^1627
        have hw : |(2624591209/5000000000 : ℝ)|=(2624591209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2822538607/5000000000 : ℝ)|^2139 ≤ (943089642159/2000000000000 : ℝ)^1627
        have hw : |(2822538607/5000000000 : ℝ)|=(2822538607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346785943/2000000000 : ℝ)|^2139 ≤ (9989933640307/100000000000000 : ℝ)^1627
        have hw : |(-346785943/2000000000 : ℝ)|=(346785943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s1_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2148887717/5000000000 : ℝ)*x 0 + (992400009/2000000000 : ℝ)*x 1 + (1860002399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148887717/5000000000 : ℝ)^2139 ≤ (16474010234497/50000000000000 : ℝ)^1627 := by
    have hnat : (2148887717 : ℕ)^2139*50000000000000^1627 ≤ 16474010234497^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148887717 5000000000 16474010234497 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992400009/2000000000 : ℝ)^2139 ≤ (39800003360667/100000000000000 : ℝ)^1627 := by
    have hnat : (992400009 : ℕ)^2139*100000000000000^1627 ≤ 39800003360667^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992400009 2000000000 39800003360667 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860002399/5000000000 : ℝ)^2139 ≤ (27251976159811/100000000000000 : ℝ)^1627 := by
    have hnat : (1860002399 : ℕ)^2139*100000000000000^1627 ≤ 27251976159811^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860002399 5000000000 27251976159811 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148887717/5000000000 : ℝ), (992400009/2000000000 : ℝ), (1860002399/5000000000 : ℝ)] ![(16474010234497/50000000000000 : ℝ), (39800003360667/100000000000000 : ℝ), (27251976159811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148887717/5000000000 : ℝ)|^2139 ≤ (16474010234497/50000000000000 : ℝ)^1627
        have hw : |(2148887717/5000000000 : ℝ)|=(2148887717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(992400009/2000000000 : ℝ)|^2139 ≤ (39800003360667/100000000000000 : ℝ)^1627
        have hw : |(992400009/2000000000 : ℝ)|=(992400009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1860002399/5000000000 : ℝ)|^2139 ≤ (27251976159811/100000000000000 : ℝ)^1627
        have hw : |(1860002399/5000000000 : ℝ)|=(1860002399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5409/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6663/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3929/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5409/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5409/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5409/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5409/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5409/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5409/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1233/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (531355426451/50000000000000000000 : ℝ) := by
    have hpowers : (1233/100000 : ℝ)^4277 ≤ (531355426451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1233 : ℕ)^4277*50000000000000000000^1024 ≤ 531355426451^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1233 100000 531355426451 50000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1233/100000 : ℝ)) (X := (531355426451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5409/20000 : ℝ) ^ (4277/1024 : ℝ) ≤ (84917045743880949/20000000000000000000 : ℝ) := by
    have hpowers : (5409/20000 : ℝ)^4277 ≤ (84917045743880949/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5409 : ℕ)^4277*20000000000000000000^1024 ≤ 84917045743880949^1024*20000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5409 20000 84917045743880949 20000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5409/20000 : ℝ)) (X := (84917045743880949/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000531355426451/25000000000000000000 : ℝ) ≤ (10000000050886879/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (25000000531355426451/25000000000000000000 : ℝ)^1024 ≤ (10000000050886879/10000000000000000 : ℝ)^4277 := by
      have hnat : (25000000531355426451 : ℕ)^1024*10000000000000000^4277 ≤ 10000000050886879^4277*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000531355426451 25000000000000000000 10000000050886879 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000050886879/10000000000000000 : ℝ)) (X := (25000000531355426451/25000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100424586291430257647/100000000000000000000 : ℝ) ≤ (500507453929193/500000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (100424586291430257647/100000000000000000000 : ℝ)^1024 ≤ (500507453929193/500000000000000 : ℝ)^4277 := by
      have hnat : (100424586291430257647 : ℕ)^1024*500000000000000^4277 ≤ 500507453929193^4277*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100424586291430257647 100000000000000000000 500507453929193 500000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500507453929193/500000000000000 : ℝ)) (X := (100424586291430257647/100000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10084917045743880949/10000000000000000000 : ℝ) ≤ (10020298106280841/10000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (10084917045743880949/10000000000000000000 : ℝ)^1024 ≤ (10020298106280841/10000000000000000 : ℝ)^4277 := by
      have hnat : (10084917045743880949 : ℕ)^1024*10000000000000000^4277 ≤ 10020298106280841^4277*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10084917045743880949 10000000000000000000 10020298106280841 10000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020298106280841/10000000000000000 : ℝ)) (X := (10084917045743880949/10000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(531355426451/50000000000000000000 : ℝ) ≤ ((4779536552059099363/4780000000000000000 : ℝ)+2*(375889914703/95600000000000 : ℝ)*(1233/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (4779536552059099363/4780000000000000000 : ℝ)+2*(375889914703/95600000000000 : ℝ)*(1233/100000 : ℝ)=(10000000050886879/10000000000000000 : ℝ) by norm_num, show 1+2*(531355426451/50000000000000000000 : ℝ)=(25000000531355426451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(84917045743880949/20000000000000000000 : ℝ)+(531355426451/50000000000000000000 : ℝ) ≤ ((4779536552059099363/4780000000000000000 : ℝ)+(375889914703/95600000000000 : ℝ)*((5409/20000 : ℝ)+(1233/100000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (4779536552059099363/4780000000000000000 : ℝ)+(375889914703/95600000000000 : ℝ)*((5409/20000 : ℝ)+(1233/100000 : ℝ))=(500507453929193/500000000000000 : ℝ) by norm_num, show 1+(84917045743880949/20000000000000000000 : ℝ)+(531355426451/50000000000000000000 : ℝ)=(100424586291430257647/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(84917045743880949/20000000000000000000 : ℝ) ≤ ((4779536552059099363/4780000000000000000 : ℝ)+2*(375889914703/95600000000000 : ℝ)*(5409/20000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (4779536552059099363/4780000000000000000 : ℝ)+2*(375889914703/95600000000000 : ℝ)*(5409/20000 : ℝ)=(10020298106280841/10000000000000000 : ℝ) by norm_num, show 1+2*(84917045743880949/20000000000000000000 : ℝ)=(10084917045743880949/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4779536552059099363/4780000000000000000 : ℝ)*(X 1 0+X 2 0)+(375889914703/95600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (1233/100000 : ℝ)) (hi := (5409/20000 : ℝ)) (c := (4779536552059099363/4780000000000000000 : ℝ)) (alpha := (375889914703/95600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4779536552059099363/4780000000000000000 : ℝ)*(X 0 1+X 2 1)+(375889914703/95600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (1233/100000 : ℝ)) (hi := (5409/20000 : ℝ)) (c := (4779536552059099363/4780000000000000000 : ℝ)) (alpha := (375889914703/95600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4779536552059099363/4780000000000000000 : ℝ)*(X 0 2+X 1 2)+(375889914703/95600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (1233/100000 : ℝ)) (hi := (5409/20000 : ℝ)) (c := (4779536552059099363/4780000000000000000 : ℝ)) (alpha := (375889914703/95600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-402340011/2000000000 : ℝ)*X 0 0+(1413268283/2500000000 : ℝ)*X 0 1+(5038869683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1081646997/2000000000 : ℝ)*X 1 0+(-1170068429/5000000000 : ℝ)*X 1 1+(5038869729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2704117489/5000000000 : ℝ)*X 2 0+(1259717403/2500000000 : ℝ)*X 2 1+(-2340137017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33566927/78125000 : ℝ)*X 0 0+(231463017/625000000 : ℝ)*X 0 1+(4978294379/10000000000 : ℝ)*X 0 2+(33566927/78125000 : ℝ)*X 1 0+(231463017/625000000 : ℝ)*X 1 1+(4978294379/10000000000 : ℝ)*X 1 2+(33566927/78125000 : ℝ)*X 2 0+(231463017/625000000 : ℝ)*X 2 1+(4978294379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201228267/1000000000 : ℝ)*X 0 0+(630839949/1250000000 : ℝ)*X 0 1+(141126943/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049836513/2000000000 : ℝ)*X 1 0+(-1733929279/10000000000 : ℝ)*X 1 1+(5645077371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624591209/5000000000 : ℝ)*X 2 0+(2822538607/5000000000 : ℝ)*X 2 1+(-346785943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148887717/5000000000 : ℝ)*X 0 0+(992400009/2000000000 : ℝ)*X 0 1+(1860002399/5000000000 : ℝ)*X 0 2+(2148887717/5000000000 : ℝ)*X 1 0+(992400009/2000000000 : ℝ)*X 1 1+(1860002399/5000000000 : ℝ)*X 1 2+(2148887717/5000000000 : ℝ)*X 2 0+(992400009/2000000000 : ℝ)*X 2 1+(1860002399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1405293881717196512918053863/239000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11125343/20000000000000 : ℝ)*(base1) + (1107316843/100000000000000 : ℝ)*(base19) + (1105209509/100000000000000 : ℝ)*(base23) + (161960087/100000000000000 : ℝ)*(upper3) + (6141011/6250000000000 : ℝ)*(upper5) + (1206263814442833/100000000000000 : ℝ)*(major0) + (1206263814442833/100000000000000 : ℝ)*(major1) + (1206263814442833/100000000000000 : ℝ)*(major2) + (1628131621137343/100000000000000 : ℝ)*(sp0) + (162813650981399/10000000000000 : ℝ)*(sp1) + (407034127980331/25000000000000 : ℝ)*(sp2) + (196096647296029/25000000000000 : ℝ)*(sp3) + (1210324041/20000000000000 : ℝ)*(sp4) + (3170947643/100000000000000 : ℝ)*(sp7) + (392194907879237/50000000000000 : ℝ)*(f.failure) + (1628137617130833/100000000000000 : ℝ)*(f.sum) + (5653596913941/4780000000000000000000000000 : ℝ)*base66 + (274323334516165379/478000000000000000000000000000000 : ℝ)*base67 + (690569293355834621/478000000000000000000000000000000 : ℝ)*base70 + (86850690086165379/478000000000000000000000000000000 : ℝ)*base71 + (14467778886661/4780000000000000000000000000 : ℝ)*base74 + (809153870646165379/478000000000000000000000000000000 : ℝ)*base75 + (811995195029834621/478000000000000000000000000000000 : ℝ)*base78 + (2030169504860165379/478000000000000000000000000000000 : ℝ)*base79 + (12080725771001/4780000000000000000000000000 : ℝ)*base82 + (2983929/5000000000000000000000 : ℝ)*base89 + (2983929/5000000000000000000000 : ℝ)*base91 + (2983929/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114052614097427398317356013/11950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6329151/25000000000000 : ℝ)*(base1) + (357835517/20000000000000 : ℝ)*(base19) + (337717301/20000000000000 : ℝ)*(base23) + (176360667/100000000000000 : ℝ)*(upper3) + (50315723/20000000000000 : ℝ)*(upper5) + (61909911953483/5000000000000 : ℝ)*(major0) + (61909911953483/5000000000000 : ℝ)*(major1) + (61909911953483/5000000000000 : ℝ)*(major2) + (8746089249/100000000000000 : ℝ)*(sp1) + (871361191/12500000000000 : ℝ)*(sp2) + (1671240565968269/100000000000000 : ℝ)*(sp4) + (167123000538483/10000000000000 : ℝ)*(sp5) + (1671231881175631/100000000000000 : ℝ)*(sp6) + (402577797016327/50000000000000 : ℝ)*(sp7) + (402577809674629/50000000000000 : ℝ)*(f.failure) + (104452533790729/6250000000000 : ℝ)*(f.sum) + (110501703743/47800000000000000000000000 : ℝ)*base65 + (120496095745818671/23900000000000000000000000000000 : ℝ)*base68 + (18907828712418671/23900000000000000000000000000000 : ℝ)*base70 + (49430720439481329/23900000000000000000000000000000 : ℝ)*base71 + (322510779553/239000000000000000000000000 : ℝ)*base74 + (211983886660681329/23900000000000000000000000000000 : ℝ)*base75 + (135635608284181329/23900000000000000000000000000000 : ℝ)*base77 + (125058027018381329/23900000000000000000000000000000 : ℝ)*base79 + (14880928947/11950000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8215993/5000000000000000000000 : ℝ)*base89 + (8215993/5000000000000000000000 : ℝ)*base91 + (8215993/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1318_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5409/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6663/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3929/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1318_s2_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-410797541/2000000000 : ℝ)*x 0 + (2743253091/5000000000 : ℝ)*x 1 + (1035677181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410797541/2000000000 : ℝ)^2139 ≤ (6240933058509/50000000000000 : ℝ)^1627 := by
    have hnat : (410797541 : ℕ)^2139*50000000000000^1627 ≤ 6240933058509^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410797541 2000000000 6240933058509 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743253091/5000000000 : ℝ)^2139 ≤ (45420822261741/100000000000000 : ℝ)^1627 := by
    have hnat : (2743253091 : ℕ)^2139*100000000000000^1627 ≤ 45420822261741^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743253091 5000000000 45420822261741 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035677181/2000000000 : ℝ)^2139 ≤ (10524327901541/25000000000000 : ℝ)^1627 := by
    have hnat : (1035677181 : ℕ)^2139*25000000000000^1627 ≤ 10524327901541^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035677181 2000000000 10524327901541 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410797541/2000000000 : ℝ), (2743253091/5000000000 : ℝ), (1035677181/2000000000 : ℝ)] ![(6240933058509/50000000000000 : ℝ), (45420822261741/100000000000000 : ℝ), (10524327901541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410797541/2000000000 : ℝ)|^2139 ≤ (6240933058509/50000000000000 : ℝ)^1627
        have hw : |(-410797541/2000000000 : ℝ)|=(410797541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743253091/5000000000 : ℝ)|^2139 ≤ (45420822261741/100000000000000 : ℝ)^1627
        have hw : |(2743253091/5000000000 : ℝ)|=(2743253091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035677181/2000000000 : ℝ)|^2139 ≤ (10524327901541/25000000000000 : ℝ)^1627
        have hw : |(1035677181/2000000000 : ℝ)|=(1035677181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1341917429/2500000000 : ℝ)*x 0 + (-2213412907/10000000000 : ℝ)*x 1 + (1294596363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341917429/2500000000 : ℝ)^2139 ≤ (44131854556391/100000000000000 : ℝ)^1627 := by
    have hnat : (1341917429 : ℕ)^2139*100000000000000^1627 ≤ 44131854556391^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341917429 2500000000 44131854556391 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213412907/10000000000 : ℝ)^2139 ≤ (215169354189/1562500000000 : ℝ)^1627 := by
    have hnat : (2213412907 : ℕ)^2139*1562500000000^1627 ≤ 215169354189^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213412907 10000000000 215169354189 1562500000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294596363/2500000000 : ℝ)^2139 ≤ (5262163345581/12500000000000 : ℝ)^1627 := by
    have hnat : (1294596363 : ℕ)^2139*12500000000000^1627 ≤ 5262163345581^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294596363 2500000000 5262163345581 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341917429/2500000000 : ℝ), (-2213412907/10000000000 : ℝ), (1294596363/2500000000 : ℝ)] ![(44131854556391/100000000000000 : ℝ), (215169354189/1562500000000 : ℝ), (5262163345581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341917429/2500000000 : ℝ)|^2139 ≤ (44131854556391/100000000000000 : ℝ)^1627
        have hw : |(1341917429/2500000000 : ℝ)|=(1341917429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213412907/10000000000 : ℝ)|^2139 ≤ (215169354189/1562500000000 : ℝ)^1627
        have hw : |(-2213412907/10000000000 : ℝ)|=(2213412907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294596363/2500000000 : ℝ)|^2139 ≤ (5262163345581/12500000000000 : ℝ)^1627
        have hw : |(1294596363/2500000000 : ℝ)|=(1294596363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367669063/10000000000 : ℝ)*x 0 + (5178386091/10000000000 : ℝ)*x 1 + (-1106706467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367669063/10000000000 : ℝ)^2139 ≤ (44131847498047/100000000000000 : ℝ)^1627 := by
    have hnat : (5367669063 : ℕ)^2139*100000000000000^1627 ≤ 44131847498047^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367669063 10000000000 44131847498047 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178386091/10000000000 : ℝ)^2139 ≤ (5262164199259/12500000000000 : ℝ)^1627 := by
    have hnat : (5178386091 : ℕ)^2139*12500000000000^1627 ≤ 5262164199259^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178386091 10000000000 5262164199259 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106706467/5000000000 : ℝ)^2139 ≤ (688541944447/5000000000000 : ℝ)^1627 := by
    have hnat : (1106706467 : ℕ)^2139*5000000000000^1627 ≤ 688541944447^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106706467 5000000000 688541944447 5000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367669063/10000000000 : ℝ), (5178386091/10000000000 : ℝ), (-1106706467/5000000000 : ℝ)] ![(44131847498047/100000000000000 : ℝ), (5262164199259/12500000000000 : ℝ), (688541944447/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367669063/10000000000 : ℝ)|^2139 ≤ (44131847498047/100000000000000 : ℝ)^1627
        have hw : |(5367669063/10000000000 : ℝ)|=(5367669063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178386091/10000000000 : ℝ)|^2139 ≤ (5262164199259/12500000000000 : ℝ)^1627
        have hw : |(5178386091/10000000000 : ℝ)|=(5178386091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106706467/5000000000 : ℝ)|^2139 ≤ (688541944447/5000000000000 : ℝ)^1627
        have hw : |(-1106706467/5000000000 : ℝ)|=(1106706467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (540756923/1250000000 : ℝ)*x 0 + (803480771/2000000000 : ℝ)*x 1 + (1164242379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540756923/1250000000 : ℝ)^2139 ≤ (33233343098581/100000000000000 : ℝ)^1627 := by
    have hnat : (540756923 : ℕ)^2139*100000000000000^1627 ≤ 33233343098581^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540756923 1250000000 33233343098581 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803480771/2000000000 : ℝ)^2139 ≤ (30151661733991/100000000000000 : ℝ)^1627 := by
    have hnat : (803480771 : ℕ)^2139*100000000000000^1627 ≤ 30151661733991^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803480771 2000000000 30151661733991 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164242379/2500000000 : ℝ)^2139 ≤ (36614995156063/100000000000000 : ℝ)^1627 := by
    have hnat : (1164242379 : ℕ)^2139*100000000000000^1627 ≤ 36614995156063^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164242379 2500000000 36614995156063 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540756923/1250000000 : ℝ), (803480771/2000000000 : ℝ), (1164242379/2500000000 : ℝ)] ![(33233343098581/100000000000000 : ℝ), (30151661733991/100000000000000 : ℝ), (36614995156063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540756923/1250000000 : ℝ)|^2139 ≤ (33233343098581/100000000000000 : ℝ)^1627
        have hw : |(540756923/1250000000 : ℝ)|=(540756923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803480771/2000000000 : ℝ)|^2139 ≤ (30151661733991/100000000000000 : ℝ)^1627
        have hw : |(803480771/2000000000 : ℝ)|=(803480771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1164242379/2500000000 : ℝ)|^2139 ≤ (36614995156063/100000000000000 : ℝ)^1627
        have hw : |(1164242379/2500000000 : ℝ)|=(1164242379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054060857/10000000000 : ℝ)*x 0 + (1036074129/2000000000 : ℝ)*x 1 + (2742251643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054060857/10000000000 : ℝ)^2139 ≤ (1248245054843/10000000000000 : ℝ)^1627 := by
    have hnat : (2054060857 : ℕ)^2139*10000000000000^1627 ≤ 1248245054843^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054060857 10000000000 1248245054843 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036074129/2000000000 : ℝ)^2139 ≤ (4211852513857/10000000000000 : ℝ)^1627 := by
    have hnat : (1036074129 : ℕ)^2139*10000000000000^1627 ≤ 4211852513857^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036074129 2000000000 4211852513857 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742251643/5000000000 : ℝ)^2139 ≤ (45399024304249/100000000000000 : ℝ)^1627 := by
    have hnat : (2742251643 : ℕ)^2139*100000000000000^1627 ≤ 45399024304249^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742251643 5000000000 45399024304249 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054060857/10000000000 : ℝ), (1036074129/2000000000 : ℝ), (2742251643/5000000000 : ℝ)] ![(1248245054843/10000000000000 : ℝ), (4211852513857/10000000000000 : ℝ), (45399024304249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054060857/10000000000 : ℝ)|^2139 ≤ (1248245054843/10000000000000 : ℝ)^1627
        have hw : |(-2054060857/10000000000 : ℝ)|=(2054060857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036074129/2000000000 : ℝ)|^2139 ≤ (4211852513857/10000000000000 : ℝ)^1627
        have hw : |(1036074129/2000000000 : ℝ)|=(1036074129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742251643/5000000000 : ℝ)|^2139 ≤ (45399024304249/100000000000000 : ℝ)^1627
        have hw : |(2742251643/5000000000 : ℝ)|=(2742251643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288461763/10000000000 : ℝ)*x 0 + (-953647301/5000000000 : ℝ)*x 1 + (1371125839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288461763/10000000000 : ℝ)^2139 ≤ (43277682333623/100000000000000 : ℝ)^1627 := by
    have hnat : (5288461763 : ℕ)^2139*100000000000000^1627 ≤ 43277682333623^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288461763 10000000000 43277682333623 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953647301/5000000000 : ℝ)^2139 ≤ (11323292586687/100000000000000 : ℝ)^1627 := by
    have hnat : (953647301 : ℕ)^2139*100000000000000^1627 ≤ 11323292586687^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953647301 5000000000 11323292586687 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371125839/2500000000 : ℝ)^2139 ≤ (4539902506603/10000000000000 : ℝ)^1627 := by
    have hnat : (1371125839 : ℕ)^2139*10000000000000^1627 ≤ 4539902506603^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371125839 2500000000 4539902506603 10000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288461763/10000000000 : ℝ), (-953647301/5000000000 : ℝ), (1371125839/2500000000 : ℝ)] ![(43277682333623/100000000000000 : ℝ), (11323292586687/100000000000000 : ℝ), (4539902506603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288461763/10000000000 : ℝ)|^2139 ≤ (43277682333623/100000000000000 : ℝ)^1627
        have hw : |(5288461763/10000000000 : ℝ)|=(5288461763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953647301/5000000000 : ℝ)|^2139 ≤ (11323292586687/100000000000000 : ℝ)^1627
        have hw : |(-953647301/5000000000 : ℝ)|=(953647301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371125839/2500000000 : ℝ)|^2139 ≤ (4539902506603/10000000000000 : ℝ)^1627
        have hw : |(1371125839/2500000000 : ℝ)|=(1371125839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288461859/10000000000 : ℝ)*x 0 + (1371125823/2500000000 : ℝ)*x 1 + (-953647279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288461859/10000000000 : ℝ)^2139 ≤ (43277683366453/100000000000000 : ℝ)^1627 := by
    have hnat : (5288461859 : ℕ)^2139*100000000000000^1627 ≤ 43277683366453^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288461859 10000000000 43277683366453 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371125823/2500000000 : ℝ)^2139 ≤ (5674878046193/12500000000000 : ℝ)^1627 := by
    have hnat : (1371125823 : ℕ)^2139*12500000000000^1627 ≤ 5674878046193^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371125823 2500000000 5674878046193 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953647279/5000000000 : ℝ)^2139 ≤ (11323292243263/100000000000000 : ℝ)^1627 := by
    have hnat : (953647279 : ℕ)^2139*100000000000000^1627 ≤ 11323292243263^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953647279 5000000000 11323292243263 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288461859/10000000000 : ℝ), (1371125823/2500000000 : ℝ), (-953647279/5000000000 : ℝ)] ![(43277683366453/100000000000000 : ℝ), (5674878046193/12500000000000 : ℝ), (11323292243263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288461859/10000000000 : ℝ)|^2139 ≤ (43277683366453/100000000000000 : ℝ)^1627
        have hw : |(5288461859/10000000000 : ℝ)|=(5288461859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371125823/2500000000 : ℝ)|^2139 ≤ (5674878046193/12500000000000 : ℝ)^1627
        have hw : |(1371125823/2500000000 : ℝ)|=(1371125823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953647279/5000000000 : ℝ)|^2139 ≤ (11323292243263/100000000000000 : ℝ)^1627
        have hw : |(-953647279/5000000000 : ℝ)|=(953647279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_s2_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081551439/2500000000 : ℝ)*x 0 + (2326423849/5000000000 : ℝ)*x 1 + (2010783309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081551439/2500000000 : ℝ)^2139 ≤ (8308715451871/25000000000000 : ℝ)^1627 := by
    have hnat : (1081551439 : ℕ)^2139*25000000000000^1627 ≤ 8308715451871^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081551439 2500000000 8308715451871 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2326423849/5000000000 : ℝ)^2139 ≤ (7314479079629/20000000000000 : ℝ)^1627 := by
    have hnat : (2326423849 : ℕ)^2139*20000000000000^1627 ≤ 7314479079629^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326423849 5000000000 7314479079629 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010783309/5000000000 : ℝ)^2139 ≤ (3774092847127/12500000000000 : ℝ)^1627 := by
    have hnat : (2010783309 : ℕ)^2139*12500000000000^1627 ≤ 3774092847127^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010783309 5000000000 3774092847127 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081551439/2500000000 : ℝ), (2326423849/5000000000 : ℝ), (2010783309/5000000000 : ℝ)] ![(8308715451871/25000000000000 : ℝ), (7314479079629/20000000000000 : ℝ), (3774092847127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081551439/2500000000 : ℝ)|^2139 ≤ (8308715451871/25000000000000 : ℝ)^1627
        have hw : |(1081551439/2500000000 : ℝ)|=(1081551439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2326423849/5000000000 : ℝ)|^2139 ≤ (7314479079629/20000000000000 : ℝ)^1627
        have hw : |(2326423849/5000000000 : ℝ)|=(2326423849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010783309/5000000000 : ℝ)|^2139 ≤ (3774092847127/12500000000000 : ℝ)^1627
        have hw : |(2010783309/5000000000 : ℝ)|=(2010783309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3929/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6663/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (969/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16203/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3929/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6663/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3929/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6663/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3929/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6663/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3929/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6663/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3929/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6663/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3929/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6663/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6663/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (1221106948389309/100000000000000000000 : ℝ) := by
    have hpowers : (6663/100000 : ℝ)^4277 ≤ (1221106948389309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6663 : ℕ)^4277*100000000000000000000^1024 ≤ 1221106948389309^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6663 100000 1221106948389309 100000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6663/100000 : ℝ)) (X := (1221106948389309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3929/20000 : ℝ) ^ (4277/1024 : ℝ) ≤ (111708162466262859/100000000000000000000 : ℝ) := by
    have hpowers : (3929/20000 : ℝ)^4277 ≤ (111708162466262859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3929 : ℕ)^4277*100000000000000000000^1024 ≤ 111708162466262859^1024*20000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3929 20000 111708162466262859 100000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3929/20000 : ℝ)) (X := (111708162466262859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001221106948389309/50000000000000000000 : ℝ) ≤ (5000029235489879/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (50001221106948389309/50000000000000000000 : ℝ)^1024 ≤ (5000029235489879/5000000000000000 : ℝ)^4277 := by
      have hnat : (50001221106948389309 : ℕ)^1024*5000000000000000^4277 ≤ 5000029235489879^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001221106948389309 50000000000000000000 5000029235489879 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029235489879/5000000000000000 : ℝ)) (X := (50001221106948389309/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12514116158676831521/12500000000000000000 : ℝ) ≤ (2500675648482323/2500000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (12514116158676831521/12500000000000000000 : ℝ)^1024 ≤ (2500675648482323/2500000000000000 : ℝ)^4277 := by
      have hnat : (12514116158676831521 : ℕ)^1024*2500000000000000^4277 ≤ 2500675648482323^4277*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514116158676831521 12500000000000000000 2500675648482323 2500000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500675648482323/2500000000000000 : ℝ)) (X := (12514116158676831521/12500000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50111708162466262859/50000000000000000000 : ℝ) ≤ (5002673358439413/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (50111708162466262859/50000000000000000000 : ℝ)^1024 ≤ (5002673358439413/5000000000000000 : ℝ)^4277 := by
      have hnat : (50111708162466262859 : ℕ)^1024*5000000000000000^4277 ≤ 5002673358439413^4277*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50111708162466262859 50000000000000000000 5002673358439413 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002673358439413/5000000000000000 : ℝ)) (X := (50111708162466262859/50000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1221106948389309/100000000000000000000 : ℝ) ≤ ((8111595217989608017/8113750000000000000 : ℝ)+2*(1322061474767/649100000000000 : ℝ)*(6663/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (8111595217989608017/8113750000000000000 : ℝ)+2*(1322061474767/649100000000000 : ℝ)*(6663/100000 : ℝ)=(5000029235489879/5000000000000000 : ℝ) by norm_num, show 1+2*(1221106948389309/100000000000000000000 : ℝ)=(50001221106948389309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(111708162466262859/100000000000000000000 : ℝ)+(1221106948389309/100000000000000000000 : ℝ) ≤ ((8111595217989608017/8113750000000000000 : ℝ)+(1322061474767/649100000000000 : ℝ)*((3929/20000 : ℝ)+(6663/100000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (8111595217989608017/8113750000000000000 : ℝ)+(1322061474767/649100000000000 : ℝ)*((3929/20000 : ℝ)+(6663/100000 : ℝ))=(2500675648482323/2500000000000000 : ℝ) by norm_num, show 1+(111708162466262859/100000000000000000000 : ℝ)+(1221106948389309/100000000000000000000 : ℝ)=(12514116158676831521/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(111708162466262859/100000000000000000000 : ℝ) ≤ ((8111595217989608017/8113750000000000000 : ℝ)+2*(1322061474767/649100000000000 : ℝ)*(3929/20000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (8111595217989608017/8113750000000000000 : ℝ)+2*(1322061474767/649100000000000 : ℝ)*(3929/20000 : ℝ)=(5002673358439413/5000000000000000 : ℝ) by norm_num, show 1+2*(111708162466262859/100000000000000000000 : ℝ)=(50111708162466262859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8111595217989608017/8113750000000000000 : ℝ)*(X 1 0+X 2 0)+(1322061474767/649100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (6663/100000 : ℝ)) (hi := (3929/20000 : ℝ)) (c := (8111595217989608017/8113750000000000000 : ℝ)) (alpha := (1322061474767/649100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8111595217989608017/8113750000000000000 : ℝ)*(X 0 1+X 2 1)+(1322061474767/649100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (6663/100000 : ℝ)) (hi := (3929/20000 : ℝ)) (c := (8111595217989608017/8113750000000000000 : ℝ)) (alpha := (1322061474767/649100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8111595217989608017/8113750000000000000 : ℝ)*(X 0 2+X 1 2)+(1322061474767/649100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (6663/100000 : ℝ)) (hi := (3929/20000 : ℝ)) (c := (8111595217989608017/8113750000000000000 : ℝ)) (alpha := (1322061474767/649100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410797541/2000000000 : ℝ)*X 0 0+(2743253091/5000000000 : ℝ)*X 0 1+(1035677181/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1341917429/2500000000 : ℝ)*X 1 0+(-2213412907/10000000000 : ℝ)*X 1 1+(1294596363/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367669063/10000000000 : ℝ)*X 2 0+(5178386091/10000000000 : ℝ)*X 2 1+(-1106706467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540756923/1250000000 : ℝ)*X 0 0+(803480771/2000000000 : ℝ)*X 0 1+(1164242379/2500000000 : ℝ)*X 0 2+(540756923/1250000000 : ℝ)*X 1 0+(803480771/2000000000 : ℝ)*X 1 1+(1164242379/2500000000 : ℝ)*X 1 2+(540756923/1250000000 : ℝ)*X 2 0+(803480771/2000000000 : ℝ)*X 2 1+(1164242379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2054060857/10000000000 : ℝ)*X 0 0+(1036074129/2000000000 : ℝ)*X 0 1+(2742251643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288461763/10000000000 : ℝ)*X 1 0+(-953647301/5000000000 : ℝ)*X 1 1+(1371125839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288461859/10000000000 : ℝ)*X 2 0+(1371125823/2500000000 : ℝ)*X 2 1+(-953647279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081551439/2500000000 : ℝ)*X 0 0+(2326423849/5000000000 : ℝ)*X 0 1+(2010783309/5000000000 : ℝ)*X 0 2+(1081551439/2500000000 : ℝ)*X 1 0+(2326423849/5000000000 : ℝ)*X 1 1+(2010783309/5000000000 : ℝ)*X 1 2+(1081551439/2500000000 : ℝ)*X 2 0+(2326423849/5000000000 : ℝ)*X 2 1+(2010783309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236371953162599833834883589/50710937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (970452463/50000000000000 : ℝ)*(base19) + (498567429/50000000000000 : ℝ)*(base23) + (11786133/4000000000000 : ℝ)*(lower2) + (679227453/100000000000000 : ℝ)*(upper3) + (62289749/50000000000000 : ℝ)*(upper5) + (601136602040653/25000000000000 : ℝ)*(major0) + (601136602040653/25000000000000 : ℝ)*(major1) + (601136602040653/25000000000000 : ℝ)*(major2) + (6490998698947/200000000000 : ℝ)*(sp0) + (162275049413377/5000000000000 : ℝ)*(sp1) + (405687741504701/12500000000000 : ℝ)*(sp2) + (62542907198823/4000000000000 : ℝ)*(sp3) + (715939793/20000000000000 : ℝ)*(sp4) + (8525905037/50000000000000 : ℝ)*(sp7) + (1563589731780649/100000000000000 : ℝ)*(f.failure) + (1622751464586233/50000000000000 : ℝ)*(f.sum) + (13774558800341/32455000000000000000000000000 : ℝ)*base66 + (129654553998209899/202843750000000000000000000000000 : ℝ)*base68 + (777648861938665101/202843750000000000000000000000000 : ℝ)*base69 + (693356256525147399/202843750000000000000000000000000 : ℝ)*base72 + (143784623653731/32455000000000000000000000000 : ℝ)*base74 + (3696182854602601/202843750000000000000000000000000 : ℝ)*base75 + (946972337525897399/202843750000000000000000000000000 : ℝ)*base78 + (969032316853616149/202843750000000000000000000000000 : ℝ)*base80 + (38097151172901/8113750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (31892333/10000000000000000000000 : ℝ)*base89 + (31892333/10000000000000000000000 : ℝ)*base91 + (31892333/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1924199224032615902612012787/202843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1849370209/100000000000000 : ℝ)*(base19) + (2161218001/100000000000000 : ℝ)*(base23) + (251312141/100000000000000 : ℝ)*(upper3) + (24600027/25000000000000 : ℝ)*(lower4) + (73991583/50000000000000 : ℝ)*(upper5) + (1218029390834563/50000000000000 : ℝ)*(major0) + (1218029390834563/50000000000000 : ℝ)*(major1) + (1218029390834563/50000000000000 : ℝ)*(major2) + (19821990199/100000000000000 : ℝ)*(sp1) + (24235195197/100000000000000 : ℝ)*(sp2) + (3288036156371629/100000000000000 : ℝ)*(sp4) + (1644007242505611/50000000000000 : ℝ)*(sp5) + (3288009759958431/100000000000000 : ℝ)*(sp6) + (792040545381383/50000000000000 : ℝ)*(sp7) + (792040545381383/50000000000000 : ℝ)*(f.failure) + (3288036156371629/100000000000000 : ℝ)*(f.sum) + (130967248523077/32455000000000000000000000000 : ℝ)*base65 + (2777573153379316571/405687500000000000000000000000000 : ℝ)*base67 + (836646036265620929/405687500000000000000000000000000 : ℝ)*base70 + (1780167881244129071/405687500000000000000000000000000 : ℝ)*base71 + (134289488760037/32455000000000000000000000000 : ℝ)*base73 + (3212827942592245929/405687500000000000000000000000000 : ℝ)*base76 + (3290114131052254071/405687500000000000000000000000000 : ℝ)*base77 + (3250187295920941571/405687500000000000000000000000000 : ℝ)*base79 + (42761814673109/16227500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (39659389/5000000000000000000000 : ℝ)*base90 + (39659389/5000000000000000000000 : ℝ)*base92 + (39659389/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1318_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3929/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6663/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1318_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1318_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1318_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1318_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1318_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (969/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16203/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
