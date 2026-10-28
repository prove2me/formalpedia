-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:04.829508+00:00
-- url     : https://prove2.me/submissions/53c1f2f7-af3c-41ad-9d3a-0b33e5b50544

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
theorem support_rectangle_w1042_s6_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-8862347/40000000 : ℝ)*x 0 + (2697705149/5000000000 : ℝ)*x 1 + (328962603/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8862347/40000000 : ℝ)^8235 ≤ (6726740076377/50000000000000 : ℝ)^6187 := by
    have hnat : (8862347 : ℕ)^8235*50000000000000^6187 ≤ 6726740076377^6187*40000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8862347 40000000 6726740076377 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697705149/5000000000 : ℝ)^8235 ≤ (43986571956211/100000000000000 : ℝ)^6187 := by
    have hnat : (2697705149 : ℕ)^8235*100000000000000^6187 ≤ 43986571956211^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697705149 5000000000 43986571956211 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328962603/625000000 : ℝ)^8235 ≤ (21279973934231/50000000000000 : ℝ)^6187 := by
    have hnat : (328962603 : ℕ)^8235*50000000000000^6187 ≤ 21279973934231^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328962603 625000000 21279973934231 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8862347/40000000 : ℝ), (2697705149/5000000000 : ℝ), (328962603/625000000 : ℝ)] ![(6726740076377/50000000000000 : ℝ), (43986571956211/100000000000000 : ℝ), (21279973934231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8862347/40000000 : ℝ)|^8235 ≤ (6726740076377/50000000000000 : ℝ)^6187
        have hw : |(-8862347/40000000 : ℝ)|=(8862347/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697705149/5000000000 : ℝ)|^8235 ≤ (43986571956211/100000000000000 : ℝ)^6187
        have hw : |(2697705149/5000000000 : ℝ)|=(2697705149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328962603/625000000 : ℝ)|^8235 ≤ (21279973934231/50000000000000 : ℝ)^6187
        have hw : |(328962603/625000000 : ℝ)|=(328962603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167037101/312500000 : ℝ)*x 0 + (-2282579617/10000000000 : ℝ)*x 1 + (5263401627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167037101/312500000 : ℝ)^8235 ≤ (43442431081997/100000000000000 : ℝ)^6187 := by
    have hnat : (167037101 : ℕ)^8235*100000000000000^6187 ≤ 43442431081997^6187*312500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167037101 312500000 43442431081997 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282579617/10000000000 : ℝ)^8235 ≤ (3499405314651/25000000000000 : ℝ)^6187 := by
    have hnat : (2282579617 : ℕ)^8235*25000000000000^6187 ≤ 3499405314651^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282579617 10000000000 3499405314651 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263401627/10000000000 : ℝ)^8235 ≤ (42559947642447/100000000000000 : ℝ)^6187 := by
    have hnat : (5263401627 : ℕ)^8235*100000000000000^6187 ≤ 42559947642447^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263401627 10000000000 42559947642447 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167037101/312500000 : ℝ), (-2282579617/10000000000 : ℝ), (5263401627/10000000000 : ℝ)] ![(43442431081997/100000000000000 : ℝ), (3499405314651/25000000000000 : ℝ), (42559947642447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167037101/312500000 : ℝ)|^8235 ≤ (43442431081997/100000000000000 : ℝ)^6187
        have hw : |(167037101/312500000 : ℝ)|=(167037101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282579617/10000000000 : ℝ)|^8235 ≤ (3499405314651/25000000000000 : ℝ)^6187
        have hw : |(-2282579617/10000000000 : ℝ)|=(2282579617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263401627/10000000000 : ℝ)|^8235 ≤ (42559947642447/100000000000000 : ℝ)^6187
        have hw : |(5263401627/10000000000 : ℝ)|=(5263401627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672593543/5000000000 : ℝ)*x 0 + (1315850433/2500000000 : ℝ)*x 1 + (-285322459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672593543/5000000000 : ℝ)^8235 ≤ (21721214751307/50000000000000 : ℝ)^6187 := by
    have hnat : (2672593543 : ℕ)^8235*50000000000000^6187 ≤ 21721214751307^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672593543 5000000000 21721214751307 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315850433/2500000000 : ℝ)^8235 ≤ (21279974386261/50000000000000 : ℝ)^6187 := by
    have hnat : (1315850433 : ℕ)^8235*50000000000000^6187 ≤ 21279974386261^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315850433 2500000000 21279974386261 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285322459/1250000000 : ℝ)^8235 ≤ (1399762170753/10000000000000 : ℝ)^6187 := by
    have hnat : (285322459 : ℕ)^8235*10000000000000^6187 ≤ 1399762170753^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285322459 1250000000 1399762170753 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672593543/5000000000 : ℝ), (1315850433/2500000000 : ℝ), (-285322459/1250000000 : ℝ)] ![(21721214751307/50000000000000 : ℝ), (21279974386261/50000000000000 : ℝ), (1399762170753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672593543/5000000000 : ℝ)|^8235 ≤ (21721214751307/50000000000000 : ℝ)^6187
        have hw : |(2672593543/5000000000 : ℝ)|=(2672593543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315850433/2500000000 : ℝ)|^8235 ≤ (21279974386261/50000000000000 : ℝ)^6187
        have hw : |(1315850433/2500000000 : ℝ)|=(1315850433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285322459/1250000000 : ℝ)|^8235 ≤ (1399762170753/10000000000000 : ℝ)^6187
        have hw : |(-285322459/1250000000 : ℝ)|=(285322459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273682713/625000000 : ℝ)*x 0 + (212605417/500000000 : ℝ)*x 1 + (563699379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273682713/625000000 : ℝ)^8235 ≤ (6663217147559/20000000000000 : ℝ)^6187 := by
    have hnat : (273682713 : ℕ)^8235*20000000000000^6187 ≤ 6663217147559^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273682713 625000000 6663217147559 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212605417/500000000 : ℝ)^8235 ≤ (32038056940211/100000000000000 : ℝ)^6187 := by
    have hnat : (212605417 : ℕ)^8235*100000000000000^6187 ≤ 32038056940211^6187*500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212605417 500000000 32038056940211 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563699379/1250000000 : ℝ)^8235 ≤ (34645857308197/100000000000000 : ℝ)^6187 := by
    have hnat : (563699379 : ℕ)^8235*100000000000000^6187 ≤ 34645857308197^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563699379 1250000000 34645857308197 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273682713/625000000 : ℝ), (212605417/500000000 : ℝ), (563699379/1250000000 : ℝ)] ![(6663217147559/20000000000000 : ℝ), (32038056940211/100000000000000 : ℝ), (34645857308197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273682713/625000000 : ℝ)|^8235 ≤ (6663217147559/20000000000000 : ℝ)^6187
        have hw : |(273682713/625000000 : ℝ)|=(273682713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212605417/500000000 : ℝ)|^8235 ≤ (32038056940211/100000000000000 : ℝ)^6187
        have hw : |(212605417/500000000 : ℝ)|=(212605417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563699379/1250000000 : ℝ)|^8235 ≤ (34645857308197/100000000000000 : ℝ)^6187
        have hw : |(563699379/1250000000 : ℝ)|=(563699379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-221559199/1000000000 : ℝ)*x 0 + (1315933781/2500000000 : ℝ)*x 1 + (1348768909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221559199/1000000000 : ℝ)^8235 ≤ (13453522503477/100000000000000 : ℝ)^6187 := by
    have hnat : (221559199 : ℕ)^8235*100000000000000^6187 ≤ 13453522503477^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221559199 1000000000 13453522503477 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315933781/2500000000 : ℝ)^8235 ≤ (21281768491013/50000000000000 : ℝ)^6187 := by
    have hnat : (1315933781 : ℕ)^8235*50000000000000^6187 ≤ 21281768491013^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315933781 2500000000 21281768491013 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348768909/2500000000 : ℝ)^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187 := by
    have hnat : (1348768909 : ℕ)^8235*50000000000000^6187 ≤ 21991470248913^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348768909 2500000000 21991470248913 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221559199/1000000000 : ℝ), (1315933781/2500000000 : ℝ), (1348768909/2500000000 : ℝ)] ![(13453522503477/100000000000000 : ℝ), (21281768491013/50000000000000 : ℝ), (21991470248913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221559199/1000000000 : ℝ)|^8235 ≤ (13453522503477/100000000000000 : ℝ)^6187
        have hw : |(-221559199/1000000000 : ℝ)|=(221559199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315933781/2500000000 : ℝ)|^8235 ≤ (21281768491013/50000000000000 : ℝ)^6187
        have hw : |(1315933781/2500000000 : ℝ)|=(1315933781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348768909/2500000000 : ℝ)|^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187
        have hw : |(1348768909/2500000000 : ℝ)|=(1348768909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328000249/2500000000 : ℝ)*x 0 + (-2150905669/10000000000 : ℝ)*x 1 + (1348768909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328000249/2500000000 : ℝ)^8235 ≤ (5385475244053/12500000000000 : ℝ)^6187 := by
    have hnat : (1328000249 : ℕ)^8235*12500000000000^6187 ≤ 5385475244053^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328000249 2500000000 5385475244053 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150905669/10000000000 : ℝ)^8235 ≤ (12933257528137/100000000000000 : ℝ)^6187 := by
    have hnat : (2150905669 : ℕ)^8235*100000000000000^6187 ≤ 12933257528137^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150905669 10000000000 12933257528137 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348768909/2500000000 : ℝ)^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187 := by
    have hnat : (1348768909 : ℕ)^8235*50000000000000^6187 ≤ 21991470248913^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348768909 2500000000 21991470248913 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328000249/2500000000 : ℝ), (-2150905669/10000000000 : ℝ), (1348768909/2500000000 : ℝ)] ![(5385475244053/12500000000000 : ℝ), (12933257528137/100000000000000 : ℝ), (21991470248913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328000249/2500000000 : ℝ)|^8235 ≤ (5385475244053/12500000000000 : ℝ)^6187
        have hw : |(1328000249/2500000000 : ℝ)|=(1328000249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2150905669/10000000000 : ℝ)|^8235 ≤ (12933257528137/100000000000000 : ℝ)^6187
        have hw : |(-2150905669/10000000000 : ℝ)|=(2150905669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348768909/2500000000 : ℝ)|^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187
        have hw : |(1348768909/2500000000 : ℝ)|=(1348768909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328000249/2500000000 : ℝ)*x 0 + (1348768909/2500000000 : ℝ)*x 1 + (-2150905669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328000249/2500000000 : ℝ)^8235 ≤ (5385475244053/12500000000000 : ℝ)^6187 := by
    have hnat : (1328000249 : ℕ)^8235*12500000000000^6187 ≤ 5385475244053^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328000249 2500000000 5385475244053 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348768909/2500000000 : ℝ)^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187 := by
    have hnat : (1348768909 : ℕ)^8235*50000000000000^6187 ≤ 21991470248913^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348768909 2500000000 21991470248913 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150905669/10000000000 : ℝ)^8235 ≤ (12933257528137/100000000000000 : ℝ)^6187 := by
    have hnat : (2150905669 : ℕ)^8235*100000000000000^6187 ≤ 12933257528137^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150905669 10000000000 12933257528137 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328000249/2500000000 : ℝ), (1348768909/2500000000 : ℝ), (-2150905669/10000000000 : ℝ)] ![(5385475244053/12500000000000 : ℝ), (21991470248913/50000000000000 : ℝ), (12933257528137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328000249/2500000000 : ℝ)|^8235 ≤ (5385475244053/12500000000000 : ℝ)^6187
        have hw : |(1328000249/2500000000 : ℝ)|=(1328000249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348768909/2500000000 : ℝ)|^8235 ≤ (21991470248913/50000000000000 : ℝ)^6187
        have hw : |(1348768909/2500000000 : ℝ)|=(1348768909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150905669/10000000000 : ℝ)|^8235 ≤ (12933257528137/100000000000000 : ℝ)^6187
        have hw : |(-2150905669/10000000000 : ℝ)|=(2150905669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s6_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189466841/5000000000 : ℝ)*x 0 + (4508944519/10000000000 : ℝ)*x 1 + (425276123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189466841/5000000000 : ℝ)^8235 ≤ (3331618978007/10000000000000 : ℝ)^6187 := by
    have hnat : (2189466841 : ℕ)^8235*10000000000000^6187 ≤ 3331618978007^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189466841 5000000000 3331618978007 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508944519/10000000000 : ℝ)^8235 ≤ (17319602725881/50000000000000 : ℝ)^6187 := by
    have hnat : (4508944519 : ℕ)^8235*50000000000000^6187 ≤ 17319602725881^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508944519 10000000000 17319602725881 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425276123/1000000000 : ℝ)^8235 ≤ (16022302377511/50000000000000 : ℝ)^6187 := by
    have hnat : (425276123 : ℕ)^8235*50000000000000^6187 ≤ 16022302377511^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425276123 1000000000 16022302377511 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189466841/5000000000 : ℝ), (4508944519/10000000000 : ℝ), (425276123/1000000000 : ℝ)] ![(3331618978007/10000000000000 : ℝ), (17319602725881/50000000000000 : ℝ), (16022302377511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189466841/5000000000 : ℝ)|^8235 ≤ (3331618978007/10000000000000 : ℝ)^6187
        have hw : |(2189466841/5000000000 : ℝ)|=(2189466841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508944519/10000000000 : ℝ)|^8235 ≤ (17319602725881/50000000000000 : ℝ)^6187
        have hw : |(4508944519/10000000000 : ℝ)|=(4508944519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425276123/1000000000 : ℝ)|^8235 ≤ (16022302377511/50000000000000 : ℝ)^6187
        have hw : |(425276123/1000000000 : ℝ)|=(425276123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11159/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (741207819654173/5000000000000000000 : ℝ) := by
    have hpowers : (11159/100000 : ℝ)^4117 ≤ (741207819654173/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11159 : ℕ)^4117*5000000000000000000^1024 ≤ 741207819654173^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11159 100000 741207819654173 5000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11159/100000 : ℝ)) (X := (741207819654173/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (9354955599997149/25000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^4117 ≤ (9354955599997149/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14049 : ℕ)^4117*25000000000000000000^1024 ≤ 9354955599997149^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 9354955599997149 25000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (9354955599997149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500741207819654173/2500000000000000000 : ℝ) ≤ (500036867247623/500000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (2500741207819654173/2500000000000000000 : ℝ)^1024 ≤ (500036867247623/500000000000000 : ℝ)^4117 := by
      have hnat : (2500741207819654173 : ℕ)^1024*500000000000000^4117 ≤ 500036867247623^4117*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500741207819654173 2500000000000000000 500036867247623 500000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500036867247623/500000000000000 : ℝ)) (X := (2500741207819654173/2500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506530497349134007/12500000000000000000 : ℝ) ≤ (2500324795595339/2500000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (12506530497349134007/12500000000000000000 : ℝ)^1024 ≤ (2500324795595339/2500000000000000 : ℝ)^4117 := by
      have hnat : (12506530497349134007 : ℕ)^1024*2500000000000000^4117 ≤ 2500324795595339^4117*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506530497349134007 12500000000000000000 2500324795595339 2500000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500324795595339/2500000000000000 : ℝ)) (X := (12506530497349134007/12500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509354955599997149/12500000000000000000 : ℝ) ≤ (2500465254952563/2500000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (12509354955599997149/12500000000000000000 : ℝ)^1024 ≤ (2500465254952563/2500000000000000 : ℝ)^4117 := by
      have hnat : (12509354955599997149 : ℕ)^1024*2500000000000000^4117 ≤ 2500465254952563^4117*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509354955599997149 12500000000000000000 2500465254952563 2500000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500465254952563/2500000000000000 : ℝ)) (X := (12509354955599997149/12500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(741207819654173/5000000000000000000 : ℝ) ≤ ((3611198979896813559/3612500000000000000 : ℝ)+2*(17557419653/9031250000000 : ℝ)*(11159/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (3611198979896813559/3612500000000000000 : ℝ)+2*(17557419653/9031250000000 : ℝ)*(11159/100000 : ℝ)=(500036867247623/500000000000000 : ℝ) by norm_num, show 1+2*(741207819654173/5000000000000000000 : ℝ)=(2500741207819654173/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9354955599997149/25000000000000000000 : ℝ)+(741207819654173/5000000000000000000 : ℝ) ≤ ((3611198979896813559/3612500000000000000 : ℝ)+(17557419653/9031250000000 : ℝ)*((14049/100000 : ℝ)+(11159/100000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (3611198979896813559/3612500000000000000 : ℝ)+(17557419653/9031250000000 : ℝ)*((14049/100000 : ℝ)+(11159/100000 : ℝ))=(2500324795595339/2500000000000000 : ℝ) by norm_num, show 1+(9354955599997149/25000000000000000000 : ℝ)+(741207819654173/5000000000000000000 : ℝ)=(12506530497349134007/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9354955599997149/25000000000000000000 : ℝ) ≤ ((3611198979896813559/3612500000000000000 : ℝ)+2*(17557419653/9031250000000 : ℝ)*(14049/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (3611198979896813559/3612500000000000000 : ℝ)+2*(17557419653/9031250000000 : ℝ)*(14049/100000 : ℝ)=(2500465254952563/2500000000000000 : ℝ) by norm_num, show 1+2*(9354955599997149/25000000000000000000 : ℝ)=(12509354955599997149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3611198979896813559/3612500000000000000 : ℝ)*(X 1 0+X 2 0)+(17557419653/9031250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3611198979896813559/3612500000000000000 : ℝ)) (alpha := (17557419653/9031250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3611198979896813559/3612500000000000000 : ℝ)*(X 0 1+X 2 1)+(17557419653/9031250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3611198979896813559/3612500000000000000 : ℝ)) (alpha := (17557419653/9031250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3611198979896813559/3612500000000000000 : ℝ)*(X 0 2+X 1 2)+(17557419653/9031250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (3611198979896813559/3612500000000000000 : ℝ)) (alpha := (17557419653/9031250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8862347/40000000 : ℝ)*X 0 0+(2697705149/5000000000 : ℝ)*X 0 1+(328962603/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167037101/312500000 : ℝ)*X 1 0+(-2282579617/10000000000 : ℝ)*X 1 1+(5263401627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672593543/5000000000 : ℝ)*X 2 0+(1315850433/2500000000 : ℝ)*X 2 1+(-285322459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273682713/625000000 : ℝ)*X 0 0+(212605417/500000000 : ℝ)*X 0 1+(563699379/1250000000 : ℝ)*X 0 2+(273682713/625000000 : ℝ)*X 1 0+(212605417/500000000 : ℝ)*X 1 1+(563699379/1250000000 : ℝ)*X 1 2+(273682713/625000000 : ℝ)*X 2 0+(212605417/500000000 : ℝ)*X 2 1+(563699379/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221559199/1000000000 : ℝ)*X 0 0+(1315933781/2500000000 : ℝ)*X 0 1+(1348768909/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328000249/2500000000 : ℝ)*X 1 0+(-2150905669/10000000000 : ℝ)*X 1 1+(1348768909/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328000249/2500000000 : ℝ)*X 2 0+(1348768909/2500000000 : ℝ)*X 2 1+(-2150905669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189466841/5000000000 : ℝ)*X 0 0+(4508944519/10000000000 : ℝ)*X 0 1+(425276123/1000000000 : ℝ)*X 0 2+(2189466841/5000000000 : ℝ)*X 1 0+(4508944519/10000000000 : ℝ)*X 1 1+(425276123/1000000000 : ℝ)*X 1 2+(2189466841/5000000000 : ℝ)*X 2 0+(4508944519/10000000000 : ℝ)*X 2 1+(425276123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157632679035738171249450687/22578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1516940843/100000000000000 : ℝ)*(base19) + (2445407/195312500000 : ℝ)*(base23) + (30990029/100000000000000 : ℝ)*(lower2) + (120750119/50000000000000 : ℝ)*(upper3) + (73267341/100000000000000 : ℝ)*(upper5) + (716192488513869/12500000000000 : ℝ)*(major0) + (716192488513869/12500000000000 : ℝ)*(major1) + (716192488513869/12500000000000 : ℝ)*(major2) + (7575305273006563/100000000000000 : ℝ)*(sp0) + (7575338774789341/100000000000000 : ℝ)*(sp1) + (7575339039681801/100000000000000 : ℝ)*(sp2) + (3883716234406427/100000000000000 : ℝ)*(sp3) + (1750936181/5000000000000 : ℝ)*(sp4) + (461147269/2000000000000 : ℝ)*(sp7) + (3883739291769877/100000000000000 : ℝ)*(f.failure) + (946917536466273/12500000000000 : ℝ)*(f.sum) + (30428022496177/3612500000000000000000000000 : ℝ)*base66 + (806755156684049771/45156250000000000000000000000000 : ℝ)*base67 + (407975529803424771/45156250000000000000000000000000 : ℝ)*base69 + (76772140915924771/45156250000000000000000000000000 : ℝ)*base71 + (18082518503571/7225000000000000000000000000 : ℝ)*base73 + (238342248728918979/45156250000000000000000000000000 : ℝ)*base76 + (160367160128762729/45156250000000000000000000000000 : ℝ)*base78 + (335411298568112271/45156250000000000000000000000000 : ℝ)*base79 + (11552549522449/1806250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (18342247/5000000000000000000000 : ℝ)*base90 + (18342247/5000000000000000000000 : ℝ)*base92 + (18342247/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58650568354120896939/12500000000000000000000000 : ℝ) := by norm_num
    linear_combination (88148997/10000000000000 : ℝ)*(base19) + (239490291/25000000000000 : ℝ)*(base23) + (23684689/25000000000000 : ℝ)*(upper3) + (34751157/100000000000000 : ℝ)*(lower4) + (4806631/5000000000000 : ℝ)*(upper5) + (2879312823660097/50000000000000 : ℝ)*(major0) + (2879312823660097/50000000000000 : ℝ)*(major1) + (2879312823660097/50000000000000 : ℝ)*(major2) + (295408249/1250000000000 : ℝ)*(sp1) + (25401682411/100000000000000 : ℝ)*(sp2) + (7613796227063459/100000000000000 : ℝ)*(sp4) + (7613771712913569/100000000000000 : ℝ)*(sp5) + (7613769867419883/100000000000000 : ℝ)*(sp6) + (1951727455587703/50000000000000 : ℝ)*(sp7) + (1951727455587703/50000000000000 : ℝ)*(f.failure) + (7613796227063459/100000000000000 : ℝ)*(f.sum) + (38891159179/12500000000000000000000000 : ℝ)*base65 + (4526598956351193/625000000000000000000000000000 : ℝ)*base68 + (5251136877601193/625000000000000000000000000000 : ℝ)*base70 + (615058902398807/625000000000000000000000000000 : ℝ)*base71 + (47382445083/25000000000000000000000000 : ℝ)*base73 + (8047768002601193/625000000000000000000000000000 : ℝ)*base76 + (3599626621148807/625000000000000000000000000000 : ℝ)*base77 + (1591293216148807/625000000000000000000000000000 : ℝ)*base79 + (150072018883/25000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7535133/2500000000000000000000 : ℝ)*base90 + (7535133/2500000000000000000000 : ℝ)*base92 + (7535133/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1042_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s7_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215632001/10000000000 : ℝ)*x 0 + (5394889731/10000000000 : ℝ)*x 1 + (1052778501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215632001/10000000000 : ℝ)^8235 ≤ (2690769176287/20000000000000 : ℝ)^6187 := by
    have hnat : (2215632001 : ℕ)^8235*20000000000000^6187 ≤ 2690769176287^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215632001 10000000000 2690769176287 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394889731/10000000000 : ℝ)^8235 ≤ (21990461626049/50000000000000 : ℝ)^6187 := by
    have hnat : (5394889731 : ℕ)^8235*50000000000000^6187 ≤ 21990461626049^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394889731 10000000000 21990461626049 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052778501/2000000000 : ℝ)^8235 ≤ (665081732157/1562500000000 : ℝ)^6187 := by
    have hnat : (1052778501 : ℕ)^8235*1562500000000^6187 ≤ 665081732157^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052778501 2000000000 665081732157 1562500000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215632001/10000000000 : ℝ), (5394889731/10000000000 : ℝ), (1052778501/2000000000 : ℝ)] ![(2690769176287/20000000000000 : ℝ), (21990461626049/50000000000000 : ℝ), (665081732157/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215632001/10000000000 : ℝ)|^8235 ≤ (2690769176287/20000000000000 : ℝ)^6187
        have hw : |(-2215632001/10000000000 : ℝ)|=(2215632001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394889731/10000000000 : ℝ)|^8235 ≤ (21990461626049/50000000000000 : ℝ)^6187
        have hw : |(5394889731/10000000000 : ℝ)|=(5394889731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052778501/2000000000 : ℝ)|^8235 ≤ (665081732157/1562500000000 : ℝ)^6187
        have hw : |(1052778501/2000000000 : ℝ)|=(1052778501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345057567/10000000000 : ℝ)*x 0 + (-2282103907/10000000000 : ℝ)*x 1 + (526389271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345057567/10000000000 : ℝ)^8235 ≤ (43441028411357/100000000000000 : ℝ)^6187 := by
    have hnat : (5345057567 : ℕ)^8235*100000000000000^6187 ≤ 43441028411357^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345057567 10000000000 43441028411357 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282103907/10000000000 : ℝ)^8235 ≤ (13993738511623/100000000000000 : ℝ)^6187 := by
    have hnat : (2282103907 : ℕ)^8235*100000000000000^6187 ≤ 13993738511623^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282103907 10000000000 13993738511623 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526389271/1000000000 : ℝ)^8235 ≤ (21282616532227/50000000000000 : ℝ)^6187 := by
    have hnat : (526389271 : ℕ)^8235*50000000000000^6187 ≤ 21282616532227^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526389271 1000000000 21282616532227 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345057567/10000000000 : ℝ), (-2282103907/10000000000 : ℝ), (526389271/1000000000 : ℝ)] ![(43441028411357/100000000000000 : ℝ), (13993738511623/100000000000000 : ℝ), (21282616532227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345057567/10000000000 : ℝ)|^8235 ≤ (43441028411357/100000000000000 : ℝ)^6187
        have hw : |(5345057567/10000000000 : ℝ)|=(5345057567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282103907/10000000000 : ℝ)|^8235 ≤ (13993738511623/100000000000000 : ℝ)^6187
        have hw : |(-2282103907/10000000000 : ℝ)|=(2282103907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526389271/1000000000 : ℝ)|^8235 ≤ (21282616532227/50000000000000 : ℝ)^6187
        have hw : |(526389271/1000000000 : ℝ)|=(526389271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672528829/5000000000 : ℝ)*x 0 + (1052778517/2000000000 : ℝ)*x 1 + (-2282103951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672528829/5000000000 : ℝ)^8235 ≤ (43441029395759/100000000000000 : ℝ)^6187 := by
    have hnat : (2672528829 : ℕ)^8235*100000000000000^6187 ≤ 43441029395759^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672528829 5000000000 43441029395759 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052778517/2000000000 : ℝ)^8235 ≤ (10641307929771/25000000000000 : ℝ)^6187 := by
    have hnat : (1052778517 : ℕ)^8235*25000000000000^6187 ≤ 10641307929771^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052778517 2000000000 10641307929771 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282103951/10000000000 : ℝ)^8235 ≤ (6996869435369/50000000000000 : ℝ)^6187 := by
    have hnat : (2282103951 : ℕ)^8235*50000000000000^6187 ≤ 6996869435369^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282103951 10000000000 6996869435369 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672528829/5000000000 : ℝ), (1052778517/2000000000 : ℝ), (-2282103951/10000000000 : ℝ)] ![(43441029395759/100000000000000 : ℝ), (10641307929771/25000000000000 : ℝ), (6996869435369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672528829/5000000000 : ℝ)|^8235 ≤ (43441029395759/100000000000000 : ℝ)^6187
        have hw : |(2672528829/5000000000 : ℝ)|=(2672528829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052778517/2000000000 : ℝ)|^8235 ≤ (10641307929771/25000000000000 : ℝ)^6187
        have hw : |(1052778517/2000000000 : ℝ)|=(1052778517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282103951/10000000000 : ℝ)|^8235 ≤ (6996869435369/50000000000000 : ℝ)^6187
        have hw : |(-2282103951/10000000000 : ℝ)|=(2282103951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378949493/10000000000 : ℝ)*x 0 + (4253091509/10000000000 : ℝ)*x 1 + (4508604907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378949493/10000000000 : ℝ)^8235 ≤ (16658174947171/50000000000000 : ℝ)^6187 := by
    have hnat : (4378949493 : ℕ)^8235*50000000000000^6187 ≤ 16658174947171^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378949493 10000000000 16658174947171 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253091509/10000000000 : ℝ)^8235 ≤ (32047917240247/100000000000000 : ℝ)^6187 := by
    have hnat : (4253091509 : ℕ)^8235*100000000000000^6187 ≤ 32047917240247^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253091509 10000000000 32047917240247 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508604907/10000000000 : ℝ)^8235 ≤ (34635732856799/100000000000000 : ℝ)^6187 := by
    have hnat : (4508604907 : ℕ)^8235*100000000000000^6187 ≤ 34635732856799^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508604907 10000000000 34635732856799 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378949493/10000000000 : ℝ), (4253091509/10000000000 : ℝ), (4508604907/10000000000 : ℝ)] ![(16658174947171/50000000000000 : ℝ), (32047917240247/100000000000000 : ℝ), (34635732856799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378949493/10000000000 : ℝ)|^8235 ≤ (16658174947171/50000000000000 : ℝ)^6187
        have hw : |(4378949493/10000000000 : ℝ)|=(4378949493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253091509/10000000000 : ℝ)|^8235 ≤ (32047917240247/100000000000000 : ℝ)^6187
        have hw : |(4253091509/10000000000 : ℝ)|=(4253091509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508604907/10000000000 : ℝ)|^8235 ≤ (34635732856799/100000000000000 : ℝ)^6187
        have hw : |(4508604907/10000000000 : ℝ)|=(4508604907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215637029/10000000000 : ℝ)*x 0 + (2632110569/5000000000 : ℝ)*x 1 + (5394560009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215637029/10000000000 : ℝ)^8235 ≤ (6726943259503/50000000000000 : ℝ)^6187 := by
    have hnat : (2215637029 : ℕ)^8235*50000000000000^6187 ≤ 6726943259503^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215637029 10000000000 6726943259503 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632110569/5000000000 : ℝ)^8235 ≤ (42568767956333/100000000000000 : ℝ)^6187 := by
    have hnat : (2632110569 : ℕ)^8235*100000000000000^6187 ≤ 42568767956333^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632110569 5000000000 42568767956333 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394560009/10000000000 : ℝ)^8235 ≤ (43977345511993/100000000000000 : ℝ)^6187 := by
    have hnat : (5394560009 : ℕ)^8235*100000000000000^6187 ≤ 43977345511993^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394560009 10000000000 43977345511993 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215637029/10000000000 : ℝ), (2632110569/5000000000 : ℝ), (5394560009/10000000000 : ℝ)] ![(6726943259503/50000000000000 : ℝ), (42568767956333/100000000000000 : ℝ), (43977345511993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215637029/10000000000 : ℝ)|^8235 ≤ (6726943259503/50000000000000 : ℝ)^6187
        have hw : |(-2215637029/10000000000 : ℝ)|=(2215637029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632110569/5000000000 : ℝ)|^8235 ≤ (42568767956333/100000000000000 : ℝ)^6187
        have hw : |(2632110569/5000000000 : ℝ)|=(2632110569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394560009/10000000000 : ℝ)|^8235 ≤ (43977345511993/100000000000000 : ℝ)^6187
        have hw : |(5394560009/10000000000 : ℝ)|=(5394560009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531212589/1000000000 : ℝ)*x 0 + (-2151436629/10000000000 : ℝ)*x 1 + (5394559741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531212589/1000000000 : ℝ)^8235 ≤ (43085150240289/100000000000000 : ℝ)^6187 := by
    have hnat : (531212589 : ℕ)^8235*100000000000000^6187 ≤ 43085150240289^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531212589 1000000000 43085150240289 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151436629/10000000000 : ℝ)^8235 ≤ (12937507143229/100000000000000 : ℝ)^6187 := by
    have hnat : (2151436629 : ℕ)^8235*100000000000000^6187 ≤ 12937507143229^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151436629 10000000000 12937507143229 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394559741/10000000000 : ℝ)^8235 ≤ (21988671302007/50000000000000 : ℝ)^6187 := by
    have hnat : (5394559741 : ℕ)^8235*50000000000000^6187 ≤ 21988671302007^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394559741 10000000000 21988671302007 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531212589/1000000000 : ℝ), (-2151436629/10000000000 : ℝ), (5394559741/10000000000 : ℝ)] ![(43085150240289/100000000000000 : ℝ), (12937507143229/100000000000000 : ℝ), (21988671302007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531212589/1000000000 : ℝ)|^8235 ≤ (43085150240289/100000000000000 : ℝ)^6187
        have hw : |(531212589/1000000000 : ℝ)|=(531212589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151436629/10000000000 : ℝ)|^8235 ≤ (12937507143229/100000000000000 : ℝ)^6187
        have hw : |(-2151436629/10000000000 : ℝ)|=(2151436629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394559741/10000000000 : ℝ)|^8235 ≤ (21988671302007/50000000000000 : ℝ)^6187
        have hw : |(5394559741/10000000000 : ℝ)|=(5394559741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312125759/10000000000 : ℝ)*x 0 + (5394560077/10000000000 : ℝ)*x 1 + (-2151436349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312125759/10000000000 : ℝ)^8235 ≤ (43085148826079/100000000000000 : ℝ)^6187 := by
    have hnat : (5312125759 : ℕ)^8235*100000000000000^6187 ≤ 43085148826079^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312125759 10000000000 43085148826079 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394560077/10000000000 : ℝ)^8235 ≤ (21988673124919/50000000000000 : ℝ)^6187 := by
    have hnat : (5394560077 : ℕ)^8235*50000000000000^6187 ≤ 21988673124919^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394560077 10000000000 21988673124919 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151436349/10000000000 : ℝ)^8235 ≤ (12937504902117/100000000000000 : ℝ)^6187 := by
    have hnat : (2151436349 : ℕ)^8235*100000000000000^6187 ≤ 12937504902117^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151436349 10000000000 12937504902117 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312125759/10000000000 : ℝ), (5394560077/10000000000 : ℝ), (-2151436349/10000000000 : ℝ)] ![(43085148826079/100000000000000 : ℝ), (21988673124919/50000000000000 : ℝ), (12937504902117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312125759/10000000000 : ℝ)|^8235 ≤ (43085148826079/100000000000000 : ℝ)^6187
        have hw : |(5312125759/10000000000 : ℝ)|=(5312125759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394560077/10000000000 : ℝ)|^8235 ≤ (21988673124919/50000000000000 : ℝ)^6187
        have hw : |(5394560077/10000000000 : ℝ)|=(5394560077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151436349/10000000000 : ℝ)|^8235 ≤ (12937504902117/100000000000000 : ℝ)^6187
        have hw : |(-2151436349/10000000000 : ℝ)|=(2151436349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s7_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875791753/2000000000 : ℝ)*x 0 + (4507965051/10000000000 : ℝ)*x 1 + (265858403/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875791753/2000000000 : ℝ)^8235 ≤ (3331644378979/10000000000000 : ℝ)^6187 := by
    have hnat : (875791753 : ℕ)^8235*10000000000000^6187 ≤ 3331644378979^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875791753 2000000000 3331644378979 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507965051/10000000000 : ℝ)^8235 ≤ (6925838089427/20000000000000 : ℝ)^6187 := by
    have hnat : (4507965051 : ℕ)^8235*20000000000000^6187 ≤ 6925838089427^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507965051 10000000000 6925838089427 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265858403/625000000 : ℝ)^8235 ≤ (3205436574771/10000000000000 : ℝ)^6187 := by
    have hnat : (265858403 : ℕ)^8235*10000000000000^6187 ≤ 3205436574771^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265858403 625000000 3205436574771 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875791753/2000000000 : ℝ), (4507965051/10000000000 : ℝ), (265858403/625000000 : ℝ)] ![(3331644378979/10000000000000 : ℝ), (6925838089427/20000000000000 : ℝ), (3205436574771/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875791753/2000000000 : ℝ)|^8235 ≤ (3331644378979/10000000000000 : ℝ)^6187
        have hw : |(875791753/2000000000 : ℝ)|=(875791753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507965051/10000000000 : ℝ)|^8235 ≤ (6925838089427/20000000000000 : ℝ)^6187
        have hw : |(4507965051/10000000000 : ℝ)|=(4507965051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265858403/625000000 : ℝ)|^8235 ≤ (3205436574771/10000000000000 : ℝ)^6187
        have hw : |(265858403/625000000 : ℝ)|=(265858403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/20000 : ℝ) ^ (4117/1024 : ℝ) ≤ (150713779236133/1000000000000000000 : ℝ) := by
    have hpowers : (2241/20000 : ℝ)^4117 ≤ (150713779236133/1000000000000000000 : ℝ)^1024 := by
      have hnat : (2241 : ℕ)^4117*1000000000000000000^1024 ≤ 150713779236133^1024*20000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 20000 150713779236133 1000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/20000 : ℝ)) (X := (150713779236133/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (18454225229193023/50000000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^4117 ≤ (18454225229193023/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14001 : ℕ)^4117*50000000000000000000^1024 ≤ 18454225229193023^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 18454225229193023 50000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (18454225229193023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500150713779236133/500000000000000000 : ℝ) ≤ (5000374820108101/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (500150713779236133/500000000000000000 : ℝ)^1024 ≤ (5000374820108101/5000000000000000 : ℝ)^4117 := by
      have hnat : (500150713779236133 : ℕ)^1024*5000000000000000^4117 ≤ 5000374820108101^4117*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500150713779236133 500000000000000000 5000374820108101 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000374820108101/5000000000000000 : ℝ)) (X := (500150713779236133/500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025989914190999673/50000000000000000000 : ℝ) ≤ (5000646307438293/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50025989914190999673/50000000000000000000 : ℝ)^1024 ≤ (5000646307438293/5000000000000000 : ℝ)^4117 := by
      have hnat : (50025989914190999673 : ℕ)^1024*5000000000000000^4117 ≤ 5000646307438293^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025989914190999673 50000000000000000000 5000646307438293 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646307438293/5000000000000000 : ℝ)) (X := (50025989914190999673/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018454225229193023/25000000000000000000 : ℝ) ≤ (1000183558953697/1000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (25018454225229193023/25000000000000000000 : ℝ)^1024 ≤ (1000183558953697/1000000000000000 : ℝ)^4117 := by
      have hnat : (25018454225229193023 : ℕ)^1024*1000000000000000^4117 ≤ 1000183558953697^4117*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018454225229193023 25000000000000000000 1000183558953697 1000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000183558953697/1000000000000000 : ℝ)) (X := (25018454225229193023/25000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(150713779236133/1000000000000000000 : ℝ) ≤ ((1164580330496053973/1165000000000000000 : ℝ)+2*(16967958137/8737500000000 : ℝ)*(2241/20000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1164580330496053973/1165000000000000000 : ℝ)+2*(16967958137/8737500000000 : ℝ)*(2241/20000 : ℝ)=(5000374820108101/5000000000000000 : ℝ) by norm_num, show 1+2*(150713779236133/1000000000000000000 : ℝ)=(500150713779236133/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18454225229193023/50000000000000000000 : ℝ)+(150713779236133/1000000000000000000 : ℝ) ≤ ((1164580330496053973/1165000000000000000 : ℝ)+(16967958137/8737500000000 : ℝ)*((14001/100000 : ℝ)+(2241/20000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (1164580330496053973/1165000000000000000 : ℝ)+(16967958137/8737500000000 : ℝ)*((14001/100000 : ℝ)+(2241/20000 : ℝ))=(5000646307438293/5000000000000000 : ℝ) by norm_num, show 1+(18454225229193023/50000000000000000000 : ℝ)+(150713779236133/1000000000000000000 : ℝ)=(50025989914190999673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18454225229193023/50000000000000000000 : ℝ) ≤ ((1164580330496053973/1165000000000000000 : ℝ)+2*(16967958137/8737500000000 : ℝ)*(14001/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1164580330496053973/1165000000000000000 : ℝ)+2*(16967958137/8737500000000 : ℝ)*(14001/100000 : ℝ)=(1000183558953697/1000000000000000 : ℝ) by norm_num, show 1+2*(18454225229193023/50000000000000000000 : ℝ)=(25018454225229193023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1164580330496053973/1165000000000000000 : ℝ)*(X 1 0+X 2 0)+(16967958137/8737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1164580330496053973/1165000000000000000 : ℝ)) (alpha := (16967958137/8737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1164580330496053973/1165000000000000000 : ℝ)*(X 0 1+X 2 1)+(16967958137/8737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1164580330496053973/1165000000000000000 : ℝ)) (alpha := (16967958137/8737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1164580330496053973/1165000000000000000 : ℝ)*(X 0 2+X 1 2)+(16967958137/8737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (1164580330496053973/1165000000000000000 : ℝ)) (alpha := (16967958137/8737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2215632001/10000000000 : ℝ)*X 0 0+(5394889731/10000000000 : ℝ)*X 0 1+(1052778501/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345057567/10000000000 : ℝ)*X 1 0+(-2282103907/10000000000 : ℝ)*X 1 1+(526389271/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672528829/5000000000 : ℝ)*X 2 0+(1052778517/2000000000 : ℝ)*X 2 1+(-2282103951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378949493/10000000000 : ℝ)*X 0 0+(4253091509/10000000000 : ℝ)*X 0 1+(4508604907/10000000000 : ℝ)*X 0 2+(4378949493/10000000000 : ℝ)*X 1 0+(4253091509/10000000000 : ℝ)*X 1 1+(4508604907/10000000000 : ℝ)*X 1 2+(4378949493/10000000000 : ℝ)*X 2 0+(4253091509/10000000000 : ℝ)*X 2 1+(4508604907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2215637029/10000000000 : ℝ)*X 0 0+(2632110569/5000000000 : ℝ)*X 0 1+(5394560009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531212589/1000000000 : ℝ)*X 1 0+(-2151436629/10000000000 : ℝ)*X 1 1+(5394559741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312125759/10000000000 : ℝ)*X 2 0+(5394560077/10000000000 : ℝ)*X 2 1+(-2151436349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875791753/2000000000 : ℝ)*X 0 0+(4507965051/10000000000 : ℝ)*X 0 1+(265858403/625000000 : ℝ)*X 0 2+(875791753/2000000000 : ℝ)*X 1 0+(4507965051/10000000000 : ℝ)*X 1 1+(265858403/625000000 : ℝ)*X 1 2+(875791753/2000000000 : ℝ)*X 2 0+(4507965051/10000000000 : ℝ)*X 2 1+(265858403/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2095227746439932257168527/1456250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (279852029/50000000000000 : ℝ)*(base19) + (15325611/2500000000000 : ℝ)*(base23) + (150304317/100000000000000 : ℝ)*(upper3) + (2048373/5000000000000 : ℝ)*(upper4) + (50473077/100000000000000 : ℝ)*(upper5) + (288687501517083/5000000000000 : ℝ)*(major0) + (288687501517083/5000000000000 : ℝ)*(major1) + (288687501517083/5000000000000 : ℝ)*(major2) + (7633772355605061/100000000000000 : ℝ)*(sp0) + (3816896278124677/50000000000000 : ℝ)*(sp1) + (1908448125732243/25000000000000 : ℝ)*(sp2) + (1956848218232427/50000000000000 : ℝ)*(sp3) + (324380443/1562500000000 : ℝ)*(sp4) + (10460305607/100000000000000 : ℝ)*(sp7) + (1956853448385231/50000000000000 : ℝ)*(f.failure) + (1908448278988353/25000000000000 : ℝ)*(f.sum) + (24474749923/11650000000000000000000000 : ℝ)*base65 + (30620876935929241/5825000000000000000000000000000 : ℝ)*base68 + (144342658779454241/5825000000000000000000000000000 : ℝ)*base70 + (89296785121054241/5825000000000000000000000000000 : ℝ)*base72 + (1271767227979/233000000000000000000000000 : ℝ)*base73 + (36676774367229241/5825000000000000000000000000000 : ℝ)*base76 + (127055051743904241/5825000000000000000000000000000 : ℝ)*base78 + (52268410250345759/5825000000000000000000000000000 : ℝ)*base79 + (48819573231/116500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (39061659/2500000000000000000000 : ℝ)*base89 + (39061659/2500000000000000000000 : ℝ)*base91 + (39061659/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114042540570493414339273959/29125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53591239/10000000000000 : ℝ)*(base19) + (245854919/25000000000000 : ℝ)*(base23) + (116738983/50000000000000 : ℝ)*(upper2) + (100187621/100000000000000 : ℝ)*(lower5) + (2901436038798387/50000000000000 : ℝ)*(major0) + (2901436038798387/50000000000000 : ℝ)*(major1) + (2901436038798387/50000000000000 : ℝ)*(major2) + (3152569759/100000000000000 : ℝ)*(sp1) + (17480400161/50000000000000 : ℝ)*(sp2) + (5254541227/100000000000000 : ℝ)*(sp3) + (7672296897273763/100000000000000 : ℝ)*(sp4) + (7672293208791613/100000000000000 : ℝ)*(sp5) + (1534452190610753/20000000000000 : ℝ)*(sp6) + (1966720936428881/50000000000000 : ℝ)*(sp7) + (3933447127398989/100000000000000 : ℝ)*(f.failure) + (7672296897273763/100000000000000 : ℝ)*(f.sum) + (2763940384979/582500000000000000000000000 : ℝ)*base65 + (169177648780208449/58250000000000000000000000000000 : ℝ)*base68 + (777879106502458449/58250000000000000000000000000000 : ℝ)*base70 + (338270936816458449/58250000000000000000000000000000 : ℝ)*base72 + (3524529643293/1165000000000000000000000000 : ℝ)*base73 + (306640407664458449/58250000000000000000000000000000 : ℝ)*base76 + (152623619317458449/58250000000000000000000000000000 : ℝ)*base78 + (448052435173458449/58250000000000000000000000000000 : ℝ)*base80 + (151209025401/582500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4015921/5000000000000000000000 : ℝ)*base89 + (4015921/5000000000000000000000 : ℝ)*base91 + (4015921/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s8_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215640719/10000000000 : ℝ)*x 0 + (26973853/50000000 : ℝ)*x 1 + (2632003031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215640719/10000000000 : ℝ)^8235 ≤ (13453916342541/100000000000000 : ℝ)^6187 := by
    have hnat : (2215640719 : ℕ)^8235*100000000000000^6187 ≤ 13453916342541^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215640719 10000000000 13453916342541 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26973853/50000000 : ℝ)^8235 ≤ (8795926115951/20000000000000 : ℝ)^6187 := by
    have hnat : (26973853 : ℕ)^8235*20000000000000^6187 ≤ 8795926115951^6187*50000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26973853 50000000 8795926115951 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632003031/5000000000 : ℝ)^8235 ≤ (1330201658473/3125000000000 : ℝ)^6187 := by
    have hnat : (2632003031 : ℕ)^8235*3125000000000^6187 ≤ 1330201658473^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632003031 5000000000 1330201658473 3125000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215640719/10000000000 : ℝ), (26973853/50000000 : ℝ), (2632003031/5000000000 : ℝ)] ![(13453916342541/100000000000000 : ℝ), (8795926115951/20000000000000 : ℝ), (1330201658473/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215640719/10000000000 : ℝ)|^8235 ≤ (13453916342541/100000000000000 : ℝ)^6187
        have hw : |(-2215640719/10000000000 : ℝ)|=(2215640719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26973853/50000000 : ℝ)|^8235 ≤ (8795926115951/20000000000000 : ℝ)^6187
        have hw : |(26973853/50000000 : ℝ)|=(26973853/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632003031/5000000000 : ℝ)|^8235 ≤ (1330201658473/3125000000000 : ℝ)^6187
        have hw : |(2632003031/5000000000 : ℝ)|=(2632003031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672514253/5000000000 : ℝ)*x 0 + (-2281992827/10000000000 : ℝ)*x 1 + (5264006151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672514253/5000000000 : ℝ)^8235 ≤ (10860178510291/25000000000000 : ℝ)^6187 := by
    have hnat : (2672514253 : ℕ)^8235*25000000000000^6187 ≤ 10860178510291^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672514253 5000000000 10860178510291 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281992827/10000000000 : ℝ)^8235 ≤ (2798566382957/20000000000000 : ℝ)^6187 := by
    have hnat : (2281992827 : ℕ)^8235*20000000000000^6187 ≤ 2798566382957^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281992827 10000000000 2798566382957 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264006151/10000000000 : ℝ)^8235 ≤ (21283227014523/50000000000000 : ℝ)^6187 := by
    have hnat : (5264006151 : ℕ)^8235*50000000000000^6187 ≤ 21283227014523^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264006151 10000000000 21283227014523 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672514253/5000000000 : ℝ), (-2281992827/10000000000 : ℝ), (5264006151/10000000000 : ℝ)] ![(10860178510291/25000000000000 : ℝ), (2798566382957/20000000000000 : ℝ), (21283227014523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672514253/5000000000 : ℝ)|^8235 ≤ (10860178510291/25000000000000 : ℝ)^6187
        have hw : |(2672514253/5000000000 : ℝ)|=(2672514253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2281992827/10000000000 : ℝ)|^8235 ≤ (2798566382957/20000000000000 : ℝ)^6187
        have hw : |(-2281992827/10000000000 : ℝ)|=(2281992827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264006151/10000000000 : ℝ)|^8235 ≤ (21283227014523/50000000000000 : ℝ)^6187
        have hw : |(5264006151/10000000000 : ℝ)|=(5264006151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106900567/200000000 : ℝ)*x 0 + (1316001539/2500000000 : ℝ)*x 1 + (-2281993027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106900567/200000000 : ℝ)^8235 ≤ (2172035617681/5000000000000 : ℝ)^6187 := by
    have hnat : (106900567 : ℕ)^8235*5000000000000^6187 ≤ 2172035617681^6187*200000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106900567 200000000 2172035617681 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316001539/2500000000 : ℝ)^8235 ≤ (42566454082861/100000000000000 : ℝ)^6187 := by
    have hnat : (1316001539 : ℕ)^8235*100000000000000^6187 ≤ 42566454082861^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316001539 2500000000 42566454082861 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281993027/10000000000 : ℝ)^8235 ≤ (13992833547103/100000000000000 : ℝ)^6187 := by
    have hnat : (2281993027 : ℕ)^8235*100000000000000^6187 ≤ 13992833547103^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281993027 10000000000 13992833547103 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106900567/200000000 : ℝ), (1316001539/2500000000 : ℝ), (-2281993027/10000000000 : ℝ)] ![(2172035617681/5000000000000 : ℝ), (42566454082861/100000000000000 : ℝ), (13992833547103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106900567/200000000 : ℝ)|^8235 ≤ (2172035617681/5000000000000 : ℝ)^6187
        have hw : |(106900567/200000000 : ℝ)|=(106900567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316001539/2500000000 : ℝ)|^8235 ≤ (42566454082861/100000000000000 : ℝ)^6187
        have hw : |(1316001539/2500000000 : ℝ)|=(1316001539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2281993027/10000000000 : ℝ)|^8235 ≤ (13992833547103/100000000000000 : ℝ)^6187
        have hw : |(-2281993027/10000000000 : ℝ)|=(2281993027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378955217/10000000000 : ℝ)*x 0 + (4253317671/10000000000 : ℝ)*x 1 + (4508377397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378955217/10000000000 : ℝ)^8235 ≤ (8329101964997/25000000000000 : ℝ)^6187 := by
    have hnat : (4378955217 : ℕ)^8235*25000000000000^6187 ≤ 8329101964997^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378955217 10000000000 8329101964997 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253317671/10000000000 : ℝ)^8235 ≤ (32050185548271/100000000000000 : ℝ)^6187 := by
    have hnat : (4253317671 : ℕ)^8235*100000000000000^6187 ≤ 32050185548271^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253317671 10000000000 32050185548271 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508377397/10000000000 : ℝ)^8235 ≤ (4329175821721/12500000000000 : ℝ)^6187 := by
    have hnat : (4508377397 : ℕ)^8235*12500000000000^6187 ≤ 4329175821721^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508377397 10000000000 4329175821721 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378955217/10000000000 : ℝ), (4253317671/10000000000 : ℝ), (4508377397/10000000000 : ℝ)] ![(8329101964997/25000000000000 : ℝ), (32050185548271/100000000000000 : ℝ), (4329175821721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378955217/10000000000 : ℝ)|^8235 ≤ (8329101964997/25000000000000 : ℝ)^6187
        have hw : |(4378955217/10000000000 : ℝ)|=(4378955217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253317671/10000000000 : ℝ)|^8235 ≤ (32050185548271/100000000000000 : ℝ)^6187
        have hw : |(4253317671/10000000000 : ℝ)|=(4253317671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508377397/10000000000 : ℝ)|^8235 ≤ (4329175821721/12500000000000 : ℝ)^6187
        have hw : |(4508377397/10000000000 : ℝ)|=(4508377397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-138477857/625000000 : ℝ)*x 0 + (526433321/1000000000 : ℝ)*x 1 + (5394442373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138477857/625000000 : ℝ)^8235 ≤ (2690791339457/20000000000000 : ℝ)^6187 := by
    have hnat : (138477857 : ℕ)^8235*20000000000000^6187 ≤ 2690791339457^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138477857 625000000 2690791339457 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526433321/1000000000 : ℝ)^8235 ≤ (2660623388203/6250000000000 : ℝ)^6187 := by
    have hnat : (526433321 : ℕ)^8235*6250000000000^6187 ≤ 2660623388203^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526433321 1000000000 2660623388203 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394442373/10000000000 : ℝ)^8235 ≤ (43976069087433/100000000000000 : ℝ)^6187 := by
    have hnat : (5394442373 : ℕ)^8235*100000000000000^6187 ≤ 43976069087433^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394442373 10000000000 43976069087433 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138477857/625000000 : ℝ), (526433321/1000000000 : ℝ), (5394442373/10000000000 : ℝ)] ![(2690791339457/20000000000000 : ℝ), (2660623388203/6250000000000 : ℝ), (43976069087433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138477857/625000000 : ℝ)|^8235 ≤ (2690791339457/20000000000000 : ℝ)^6187
        have hw : |(-138477857/625000000 : ℝ)|=(138477857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526433321/1000000000 : ℝ)|^8235 ≤ (2660623388203/6250000000000 : ℝ)^6187
        have hw : |(526433321/1000000000 : ℝ)|=(526433321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394442373/10000000000 : ℝ)|^8235 ≤ (43976069087433/100000000000000 : ℝ)^6187
        have hw : |(5394442373/10000000000 : ℝ)|=(5394442373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312155109/10000000000 : ℝ)*x 0 + (-2151556313/10000000000 : ℝ)*x 1 + (337152649/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312155109/10000000000 : ℝ)^8235 ≤ (1723418626971/4000000000000 : ℝ)^6187 := by
    have hnat : (5312155109 : ℕ)^8235*4000000000000^6187 ≤ 1723418626971^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312155109 10000000000 1723418626971 4000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151556313/10000000000 : ℝ)^8235 ≤ (1293846509937/10000000000000 : ℝ)^6187 := by
    have hnat : (2151556313 : ℕ)^8235*10000000000000^6187 ≤ 1293846509937^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151556313 10000000000 1293846509937 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337152649/625000000 : ℝ)^8235 ≤ (4397606920679/10000000000000 : ℝ)^6187 := by
    have hnat : (337152649 : ℕ)^8235*10000000000000^6187 ≤ 4397606920679^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337152649 625000000 4397606920679 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312155109/10000000000 : ℝ), (-2151556313/10000000000 : ℝ), (337152649/625000000 : ℝ)] ![(1723418626971/4000000000000 : ℝ), (1293846509937/10000000000000 : ℝ), (4397606920679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312155109/10000000000 : ℝ)|^8235 ≤ (1723418626971/4000000000000 : ℝ)^6187
        have hw : |(5312155109/10000000000 : ℝ)|=(5312155109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151556313/10000000000 : ℝ)|^8235 ≤ (1293846509937/10000000000000 : ℝ)^6187
        have hw : |(-2151556313/10000000000 : ℝ)|=(2151556313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337152649/625000000 : ℝ)|^8235 ≤ (4397606920679/10000000000000 : ℝ)^6187
        have hw : |(337152649/625000000 : ℝ)|=(337152649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656077183/5000000000 : ℝ)*x 0 + (269722113/500000000 : ℝ)*x 1 + (-537889371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656077183/5000000000 : ℝ)^8235 ≤ (8617091530641/20000000000000 : ℝ)^6187 := by
    have hnat : (2656077183 : ℕ)^8235*20000000000000^6187 ≤ 8617091530641^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656077183 5000000000 8617091530641 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269722113/500000000 : ℝ)^8235 ≤ (43976067861317/100000000000000 : ℝ)^6187 := by
    have hnat : (269722113 : ℕ)^8235*100000000000000^6187 ≤ 43976067861317^6187*500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269722113 500000000 43976067861317 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537889371/2500000000 : ℝ)^8235 ≤ (6469237236097/50000000000000 : ℝ)^6187 := by
    have hnat : (537889371 : ℕ)^8235*50000000000000^6187 ≤ 6469237236097^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537889371 2500000000 6469237236097 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656077183/5000000000 : ℝ), (269722113/500000000 : ℝ), (-537889371/2500000000 : ℝ)] ![(8617091530641/20000000000000 : ℝ), (43976067861317/100000000000000 : ℝ), (6469237236097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656077183/5000000000 : ℝ)|^8235 ≤ (8617091530641/20000000000000 : ℝ)^6187
        have hw : |(2656077183/5000000000 : ℝ)|=(2656077183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269722113/500000000 : ℝ)|^8235 ≤ (43976067861317/100000000000000 : ℝ)^6187
        have hw : |(269722113/500000000 : ℝ)|=(269722113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537889371/2500000000 : ℝ)|^8235 ≤ (6469237236097/50000000000000 : ℝ)^6187
        have hw : |(-537889371/2500000000 : ℝ)|=(537889371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s8_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189482259/5000000000 : ℝ)*x 0 + (2253869629/5000000000 : ℝ)*x 1 + (4253958809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189482259/5000000000 : ℝ)^8235 ≤ (16658251024577/50000000000000 : ℝ)^6187 := by
    have hnat : (2189482259 : ℕ)^8235*50000000000000^6187 ≤ 16658251024577^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189482259 5000000000 16658251024577 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253869629/5000000000 : ℝ)^8235 ≤ (346268818287/1000000000000 : ℝ)^6187 := by
    have hnat : (2253869629 : ℕ)^8235*1000000000000^6187 ≤ 346268818287^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253869629 5000000000 346268818287 1000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253958809/10000000000 : ℝ)^8235 ≤ (3205661610491/10000000000000 : ℝ)^6187 := by
    have hnat : (4253958809 : ℕ)^8235*10000000000000^6187 ≤ 3205661610491^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253958809 10000000000 3205661610491 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189482259/5000000000 : ℝ), (2253869629/5000000000 : ℝ), (4253958809/10000000000 : ℝ)] ![(16658251024577/50000000000000 : ℝ), (346268818287/1000000000000 : ℝ), (3205661610491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189482259/5000000000 : ℝ)|^8235 ≤ (16658251024577/50000000000000 : ℝ)^6187
        have hw : |(2189482259/5000000000 : ℝ)|=(2189482259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253869629/5000000000 : ℝ)|^8235 ≤ (346268818287/1000000000000 : ℝ)^6187
        have hw : |(2253869629/5000000000 : ℝ)|=(2253869629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253958809/10000000000 : ℝ)|^8235 ≤ (3205661610491/10000000000000 : ℝ)^6187
        have hw : |(4253958809/10000000000 : ℝ)|=(4253958809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3497/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/6250 : ℝ) ^ (4117/1024 : ℝ) ≤ (15130952167393507/100000000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^4117 ≤ (15130952167393507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (701 : ℕ)^4117*100000000000000000000^1024 ≤ 15130952167393507^1024*6250^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 15130952167393507 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (15130952167393507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (4117/1024 : ℝ) ≤ (3679200434167291/10000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^4117 ≤ (3679200434167291/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4117*10000000000000000000^1024 ≤ 3679200434167291^1024*10000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 3679200434167291 10000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (3679200434167291/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015130952167393507/50000000000000000000 : ℝ) ≤ (10000752603062319/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50015130952167393507/50000000000000000000 : ℝ)^1024 ≤ (10000752603062319/10000000000000000 : ℝ)^4117 := by
      have hnat : (50015130952167393507 : ℕ)^1024*10000000000000000^4117 ≤ 10000752603062319^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015130952167393507 50000000000000000000 10000752603062319 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000752603062319/10000000000000000 : ℝ)) (X := (50015130952167393507/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051922956509066417/100000000000000000000 : ℝ) ≤ (10001291200883909/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (100051922956509066417/100000000000000000000 : ℝ)^1024 ≤ (10001291200883909/10000000000000000 : ℝ)^4117 := by
      have hnat : (100051922956509066417 : ℕ)^1024*10000000000000000^4117 ≤ 10001291200883909^4117*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051922956509066417 100000000000000000000 10001291200883909 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001291200883909/10000000000000000 : ℝ)) (X := (100051922956509066417/100000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003679200434167291/5000000000000000000 : ℝ) ≤ (10001829798705499/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (5003679200434167291/5000000000000000000 : ℝ)^1024 ≤ (10001829798705499/10000000000000000 : ℝ)^4117 := by
      have hnat : (5003679200434167291 : ℕ)^1024*10000000000000000^4117 ≤ 10001829798705499^4117*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003679200434167291 5000000000000000000 10001829798705499 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001829798705499/10000000000000000 : ℝ)) (X := (5003679200434167291/5000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15130952167393507/100000000000000000000 : ℝ) ≤ ((13865002947280483013/13870000000000000000 : ℝ)+2*(53859782159/27740000000000 : ℝ)*(701/6250 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (13865002947280483013/13870000000000000000 : ℝ)+2*(53859782159/27740000000000 : ℝ)*(701/6250 : ℝ)=(10000752603062319/10000000000000000 : ℝ) by norm_num, show 1+2*(15130952167393507/100000000000000000000 : ℝ)=(50015130952167393507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3679200434167291/10000000000000000000 : ℝ)+(15130952167393507/100000000000000000000 : ℝ) ≤ ((13865002947280483013/13870000000000000000 : ℝ)+(53859782159/27740000000000 : ℝ)*((1399/10000 : ℝ)+(701/6250 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (13865002947280483013/13870000000000000000 : ℝ)+(53859782159/27740000000000 : ℝ)*((1399/10000 : ℝ)+(701/6250 : ℝ))=(10001291200883909/10000000000000000 : ℝ) by norm_num, show 1+(3679200434167291/10000000000000000000 : ℝ)+(15130952167393507/100000000000000000000 : ℝ)=(100051922956509066417/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3679200434167291/10000000000000000000 : ℝ) ≤ ((13865002947280483013/13870000000000000000 : ℝ)+2*(53859782159/27740000000000 : ℝ)*(1399/10000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (13865002947280483013/13870000000000000000 : ℝ)+2*(53859782159/27740000000000 : ℝ)*(1399/10000 : ℝ)=(10001829798705499/10000000000000000 : ℝ) by norm_num, show 1+2*(3679200434167291/10000000000000000000 : ℝ)=(5003679200434167291/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13865002947280483013/13870000000000000000 : ℝ)*(X 1 0+X 2 0)+(53859782159/27740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13865002947280483013/13870000000000000000 : ℝ)) (alpha := (53859782159/27740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13865002947280483013/13870000000000000000 : ℝ)*(X 0 1+X 2 1)+(53859782159/27740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13865002947280483013/13870000000000000000 : ℝ)) (alpha := (53859782159/27740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13865002947280483013/13870000000000000000 : ℝ)*(X 0 2+X 1 2)+(53859782159/27740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13865002947280483013/13870000000000000000 : ℝ)) (alpha := (53859782159/27740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2215640719/10000000000 : ℝ)*X 0 0+(26973853/50000000 : ℝ)*X 0 1+(2632003031/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672514253/5000000000 : ℝ)*X 1 0+(-2281992827/10000000000 : ℝ)*X 1 1+(5264006151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106900567/200000000 : ℝ)*X 2 0+(1316001539/2500000000 : ℝ)*X 2 1+(-2281993027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378955217/10000000000 : ℝ)*X 0 0+(4253317671/10000000000 : ℝ)*X 0 1+(4508377397/10000000000 : ℝ)*X 0 2+(4378955217/10000000000 : ℝ)*X 1 0+(4253317671/10000000000 : ℝ)*X 1 1+(4508377397/10000000000 : ℝ)*X 1 2+(4378955217/10000000000 : ℝ)*X 2 0+(4253317671/10000000000 : ℝ)*X 2 1+(4508377397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-138477857/625000000 : ℝ)*X 0 0+(526433321/1000000000 : ℝ)*X 0 1+(5394442373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312155109/10000000000 : ℝ)*X 1 0+(-2151556313/10000000000 : ℝ)*X 1 1+(337152649/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656077183/5000000000 : ℝ)*X 2 0+(269722113/500000000 : ℝ)*X 2 1+(-537889371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189482259/5000000000 : ℝ)*X 0 0+(2253869629/5000000000 : ℝ)*X 0 1+(4253958809/10000000000 : ℝ)*X 0 2+(2189482259/5000000000 : ℝ)*X 1 0+(2253869629/5000000000 : ℝ)*X 1 1+(4253958809/10000000000 : ℝ)*X 1 2+(2189482259/5000000000 : ℝ)*X 2 0+(2253869629/5000000000 : ℝ)*X 2 1+(4253958809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2021416564502369548961027871/346750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246129273/20000000000000 : ℝ)*(base19) + (282365389/25000000000000 : ℝ)*(base23) + (13855749/20000000000000 : ℝ)*(upper2) + (13327493/5000000000000 : ℝ)*(upper3) + (1015687/25000000000000 : ℝ)*(upper4) + (5784048429760689/100000000000000 : ℝ)*(major0) + (5784048429760689/100000000000000 : ℝ)*(major1) + (5784048429760689/100000000000000 : ℝ)*(major2) + (7647379584973137/100000000000000 : ℝ)*(sp0) + (7647407820465349/100000000000000 : ℝ)*(sp1) + (3823703960825079/50000000000000 : ℝ)*(sp2) + (3920667148537031/100000000000000 : ℝ)*(sp3) + (29466138577/100000000000000 : ℝ)*(sp4) + (5116388089/25000000000000 : ℝ)*(sp7) + (3920687614089387/100000000000000 : ℝ)*(f.failure) + (3823704525555857/50000000000000 : ℝ)*(f.sum) + (1202437992429/277400000000000000000000000 : ℝ)*base66 + (15192956919657824043/1387000000000000000000000000000000 : ℝ)*base68 + (25630535546366824043/1387000000000000000000000000000000 : ℝ)*base70 + (8650540221572175957/1387000000000000000000000000000000 : ℝ)*base71 + (10868724993511/1387000000000000000000000000 : ℝ)*base74 + (32682712058174824043/1387000000000000000000000000000000 : ℝ)*base76 + (22836774137649824043/1387000000000000000000000000000000 : ℝ)*base78 + (7910871651243824043/1387000000000000000000000000000000 : ℝ)*base80 + (490284402679/86687500000000000000000000 : ℝ)*base82 + (66175143/5000000000000000000000 : ℝ)*base89 + (66175143/5000000000000000000000 : ℝ)*base91 + (66175143/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3917892501367291161807194139/346750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302876179/20000000000000 : ℝ)*(base19) + (411868449/100000000000000 : ℝ)*(base23) + (206112289/100000000000000 : ℝ)*(upper2) + (62394853/100000000000000 : ℝ)*(upper3) + (21001433/50000000000000 : ℝ)*(upper5) + (2906567921009099/50000000000000 : ℝ)*(major0) + (2906567921009099/50000000000000 : ℝ)*(major1) + (2906567921009099/50000000000000 : ℝ)*(major2) + (712318701/4000000000000 : ℝ)*(sp0) + (16785922609/25000000000000 : ℝ)*(sp1) + (153716982637537/2000000000000 : ℝ)*(sp4) + (1921449570443261/25000000000000 : ℝ)*(sp5) + (3842933263987963/50000000000000 : ℝ)*(sp6) + (3940404367562117/100000000000000 : ℝ)*(sp7) + (3940404367562117/100000000000000 : ℝ)*(f.failure) + (12297387103751/160000000000 : ℝ)*(f.sum) + (5893789052763/277400000000000000000000000 : ℝ)*base66 + (9984518960717435287/693500000000000000000000000000000 : ℝ)*base67 + (6875352098002935287/693500000000000000000000000000000 : ℝ)*base69 + (2619429448475435287/693500000000000000000000000000000 : ℝ)*base71 + (1601759192843/346750000000000000000000000 : ℝ)*base74 + (759574658039064713/693500000000000000000000000000000 : ℝ)*base76 + (9054317121951435287/693500000000000000000000000000000 : ℝ)*base77 + (1643450506092564713/693500000000000000000000000000000 : ℝ)*base80 + (712228082979/1387000000000000000000000000 : ℝ)*base81 + (5511113/5000000000000000000000 : ℝ)*base89 + (5511113/5000000000000000000000 : ℝ)*base91 + (5511113/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1042_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1042_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1042_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1042_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
