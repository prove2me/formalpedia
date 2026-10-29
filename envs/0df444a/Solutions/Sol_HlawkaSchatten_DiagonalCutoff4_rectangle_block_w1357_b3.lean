-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:10:25.164256+00:00
-- url     : https://prove2.me/submissions/f21fb504-3cf5-4069-9fdf-dfeff19eda39

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
theorem support_rectangle_w1357_box_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-186501167/1000000000 : ℝ)*x 0 + (336832003/625000000 : ℝ)*x 1 + (1347328183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186501167/1000000000 : ℝ)^4317 ≤ (11063454608223/100000000000000 : ℝ)^3293 := by
    have hnat : (186501167 : ℕ)^4317*100000000000000^3293 ≤ 11063454608223^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186501167 1000000000 11063454608223 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336832003/625000000 : ℝ)^4317 ≤ (44468268991653/100000000000000 : ℝ)^3293 := by
    have hnat : (336832003 : ℕ)^4317*100000000000000^3293 ≤ 44468268991653^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336832003 625000000 44468268991653 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347328183/2500000000 : ℝ)^4317 ≤ (5558534548811/12500000000000 : ℝ)^3293 := by
    have hnat : (1347328183 : ℕ)^4317*12500000000000^3293 ≤ 5558534548811^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347328183 2500000000 5558534548811 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-186501167/1000000000 : ℝ), (336832003/625000000 : ℝ), (1347328183/2500000000 : ℝ)] ![(11063454608223/100000000000000 : ℝ), (44468268991653/100000000000000 : ℝ), (5558534548811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-186501167/1000000000 : ℝ)|^4317 ≤ (11063454608223/100000000000000 : ℝ)^3293
        have hw : |(-186501167/1000000000 : ℝ)|=(186501167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336832003/625000000 : ℝ)|^4317 ≤ (44468268991653/100000000000000 : ℝ)^3293
        have hw : |(336832003/625000000 : ℝ)|=(336832003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347328183/2500000000 : ℝ)|^4317 ≤ (5558534548811/12500000000000 : ℝ)^3293
        have hw : |(1347328183/2500000000 : ℝ)|=(1347328183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528536299/1000000000 : ℝ)*x 0 + (-501875001/2500000000 : ℝ)*x 1 + (5389311991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528536299/1000000000 : ℝ)^4317 ≤ (1733889525921/4000000000000 : ℝ)^3293 := by
    have hnat : (528536299 : ℕ)^4317*4000000000000^3293 ≤ 1733889525921^3293*1000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528536299 1000000000 1733889525921 4000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501875001/2500000000 : ℝ)^4317 ≤ (12184493470137/100000000000000 : ℝ)^3293 := by
    have hnat : (501875001 : ℕ)^4317*100000000000000^3293 ≤ 12184493470137^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501875001 2500000000 12184493470137 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389311991/10000000000 : ℝ)^4317 ≤ (11117067093771/25000000000000 : ℝ)^3293 := by
    have hnat : (5389311991 : ℕ)^4317*25000000000000^3293 ≤ 11117067093771^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389311991 10000000000 11117067093771 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528536299/1000000000 : ℝ), (-501875001/2500000000 : ℝ), (5389311991/10000000000 : ℝ)] ![(1733889525921/4000000000000 : ℝ), (12184493470137/100000000000000 : ℝ), (11117067093771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528536299/1000000000 : ℝ)|^4317 ≤ (1733889525921/4000000000000 : ℝ)^3293
        have hw : |(528536299/1000000000 : ℝ)|=(528536299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501875001/2500000000 : ℝ)|^4317 ≤ (12184493470137/100000000000000 : ℝ)^3293
        have hw : |(-501875001/2500000000 : ℝ)|=(501875001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389311991/10000000000 : ℝ)|^4317 ≤ (11117067093771/25000000000000 : ℝ)^3293
        have hw : |(5389311991/10000000000 : ℝ)|=(5389311991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285362793/10000000000 : ℝ)*x 0 + (5389312189/10000000000 : ℝ)*x 1 + (-803/4000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285362793/10000000000 : ℝ)^4317 ≤ (43347236029941/100000000000000 : ℝ)^3293 := by
    have hnat : (5285362793 : ℕ)^4317*100000000000000^3293 ≤ 43347236029941^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285362793 10000000000 43347236029941 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389312189/10000000000 : ℝ)^4317 ≤ (11117067629213/25000000000000 : ℝ)^3293 := by
    have hnat : (5389312189 : ℕ)^4317*25000000000000^3293 ≤ 11117067629213^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389312189 10000000000 11117067629213 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803/4000 : ℝ)^4317 ≤ (12184493438309/100000000000000 : ℝ)^3293 := by
    have hnat : (803 : ℕ)^4317*100000000000000^3293 ≤ 12184493438309^3293*4000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803 4000 12184493438309 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285362793/10000000000 : ℝ), (5389312189/10000000000 : ℝ), (-803/4000 : ℝ)] ![(43347236029941/100000000000000 : ℝ), (11117067629213/25000000000000 : ℝ), (12184493438309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285362793/10000000000 : ℝ)|^4317 ≤ (43347236029941/100000000000000 : ℝ)^3293
        have hw : |(5285362793/10000000000 : ℝ)|=(5285362793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389312189/10000000000 : ℝ)|^4317 ≤ (11117067629213/25000000000000 : ℝ)^3293
        have hw : |(5389312189/10000000000 : ℝ)|=(5389312189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-803/4000 : ℝ)|^4317 ≤ (12184493438309/100000000000000 : ℝ)^3293
        have hw : |(-803/4000 : ℝ)|=(803/4000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4470555887/10000000000 : ℝ)*x 0 + (531581323/1250000000 : ℝ)*x 1 + (1063162719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470555887/10000000000 : ℝ)^4317 ≤ (6960926035361/20000000000000 : ℝ)^3293 := by
    have hnat : (4470555887 : ℕ)^4317*20000000000000^3293 ≤ 6960926035361^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470555887 10000000000 6960926035361 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531581323/1250000000 : ℝ)^4317 ≤ (260781467479/800000000000 : ℝ)^3293 := by
    have hnat : (531581323 : ℕ)^4317*800000000000^3293 ≤ 260781467479^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531581323 1250000000 260781467479 800000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063162719/2500000000 : ℝ)^4317 ≤ (16298843184573/50000000000000 : ℝ)^3293 := by
    have hnat : (1063162719 : ℕ)^4317*50000000000000^3293 ≤ 16298843184573^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063162719 2500000000 16298843184573 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470555887/10000000000 : ℝ), (531581323/1250000000 : ℝ), (1063162719/2500000000 : ℝ)] ![(6960926035361/20000000000000 : ℝ), (260781467479/800000000000 : ℝ), (16298843184573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470555887/10000000000 : ℝ)|^4317 ≤ (6960926035361/20000000000000 : ℝ)^3293
        have hw : |(4470555887/10000000000 : ℝ)|=(4470555887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531581323/1250000000 : ℝ)|^4317 ≤ (260781467479/800000000000 : ℝ)^3293
        have hw : |(531581323/1250000000 : ℝ)|=(531581323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063162719/2500000000 : ℝ)|^4317 ≤ (16298843184573/50000000000000 : ℝ)^3293
        have hw : |(1063162719/2500000000 : ℝ)|=(1063162719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199904529/10000000000 : ℝ)*x 0 + (5265249449/10000000000 : ℝ)*x 1 + (329078177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199904529/10000000000 : ℝ)^4317 ≤ (2747552402927/20000000000000 : ℝ)^3293 := by
    have hnat : (2199904529 : ℕ)^4317*20000000000000^3293 ≤ 2747552402927^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199904529 10000000000 2747552402927 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265249449/10000000000 : ℝ)^4317 ≤ (8626222311929/20000000000000 : ℝ)^3293 := by
    have hnat : (5265249449 : ℕ)^4317*20000000000000^3293 ≤ 8626222311929^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265249449 10000000000 8626222311929 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329078177/625000000 : ℝ)^4317 ≤ (2156556320581/5000000000000 : ℝ)^3293 := by
    have hnat : (329078177 : ℕ)^4317*5000000000000^3293 ≤ 2156556320581^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329078177 625000000 2156556320581 5000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199904529/10000000000 : ℝ), (5265249449/10000000000 : ℝ), (329078177/625000000 : ℝ)] ![(2747552402927/20000000000000 : ℝ), (8626222311929/20000000000000 : ℝ), (2156556320581/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199904529/10000000000 : ℝ)|^4317 ≤ (2747552402927/20000000000000 : ℝ)^3293
        have hw : |(-2199904529/10000000000 : ℝ)|=(2199904529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265249449/10000000000 : ℝ)|^4317 ≤ (8626222311929/20000000000000 : ℝ)^3293
        have hw : |(5265249449/10000000000 : ℝ)|=(5265249449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329078177/625000000 : ℝ)|^4317 ≤ (2156556320581/5000000000000 : ℝ)^3293
        have hw : |(329078177/625000000 : ℝ)|=(329078177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268622303/500000000 : ℝ)*x 0 + (-257173299/1250000000 : ℝ)*x 1 + (1053050117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268622303/500000000 : ℝ)^4317 ≤ (44285918274903/100000000000000 : ℝ)^3293 := by
    have hnat : (268622303 : ℕ)^4317*100000000000000^3293 ≤ 44285918274903^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268622303 500000000 44285918274903 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257173299/1250000000 : ℝ)^4317 ≤ (314573948827/2500000000000 : ℝ)^3293 := by
    have hnat : (257173299 : ℕ)^4317*2500000000000^3293 ≤ 314573948827^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257173299 1250000000 314573948827 2500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053050117/2000000000 : ℝ)^4317 ≤ (21565561879549/50000000000000 : ℝ)^3293 := by
    have hnat : (1053050117 : ℕ)^4317*50000000000000^3293 ≤ 21565561879549^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053050117 2000000000 21565561879549 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268622303/500000000 : ℝ), (-257173299/1250000000 : ℝ), (1053050117/2000000000 : ℝ)] ![(44285918274903/100000000000000 : ℝ), (314573948827/2500000000000 : ℝ), (21565561879549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268622303/500000000 : ℝ)|^4317 ≤ (44285918274903/100000000000000 : ℝ)^3293
        have hw : |(268622303/500000000 : ℝ)|=(268622303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257173299/1250000000 : ℝ)|^4317 ≤ (314573948827/2500000000000 : ℝ)^3293
        have hw : |(-257173299/1250000000 : ℝ)|=(257173299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053050117/2000000000 : ℝ)|^4317 ≤ (21565561879549/50000000000000 : ℝ)^3293
        have hw : |(1053050117/2000000000 : ℝ)|=(1053050117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074489077/2000000000 : ℝ)*x 0 + (658156409/1250000000 : ℝ)*x 1 + (-2057386381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074489077/2000000000 : ℝ)^4317 ≤ (8857182196107/20000000000000 : ℝ)^3293 := by
    have hnat : (1074489077 : ℕ)^4317*20000000000000^3293 ≤ 8857182196107^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074489077 2000000000 8857182196107 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658156409/1250000000 : ℝ)^4317 ≤ (43131131136761/100000000000000 : ℝ)^3293 := by
    have hnat : (658156409 : ℕ)^4317*100000000000000^3293 ≤ 43131131136761^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658156409 1250000000 43131131136761 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057386381/10000000000 : ℝ)^4317 ≤ (12582957864883/100000000000000 : ℝ)^3293 := by
    have hnat : (2057386381 : ℕ)^4317*100000000000000^3293 ≤ 12582957864883^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057386381 10000000000 12582957864883 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074489077/2000000000 : ℝ), (658156409/1250000000 : ℝ), (-2057386381/10000000000 : ℝ)] ![(8857182196107/20000000000000 : ℝ), (43131131136761/100000000000000 : ℝ), (12582957864883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074489077/2000000000 : ℝ)|^4317 ≤ (8857182196107/20000000000000 : ℝ)^3293
        have hw : |(1074489077/2000000000 : ℝ)|=(1074489077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658156409/1250000000 : ℝ)|^4317 ≤ (43131131136761/100000000000000 : ℝ)^3293
        have hw : |(658156409/1250000000 : ℝ)|=(658156409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057386381/10000000000 : ℝ)|^4317 ≤ (12582957864883/100000000000000 : ℝ)^3293
        have hw : |(-2057386381/10000000000 : ℝ)|=(2057386381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086963361/5000000000 : ℝ)*x 0 + (2200456137/5000000000 : ℝ)*x 1 + (1100228041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086963361/5000000000 : ℝ)^4317 ≤ (7952221007499/25000000000000 : ℝ)^3293 := by
    have hnat : (2086963361 : ℕ)^4317*25000000000000^3293 ≤ 7952221007499^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086963361 5000000000 7952221007499 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200456137/5000000000 : ℝ)^4317 ≤ (8523889635089/25000000000000 : ℝ)^3293 := by
    have hnat : (2200456137 : ℕ)^4317*25000000000000^3293 ≤ 8523889635089^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200456137 5000000000 8523889635089 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100228041/2500000000 : ℝ)^4317 ≤ (17047778711569/50000000000000 : ℝ)^3293 := by
    have hnat : (1100228041 : ℕ)^4317*50000000000000^3293 ≤ 17047778711569^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100228041 2500000000 17047778711569 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086963361/5000000000 : ℝ), (2200456137/5000000000 : ℝ), (1100228041/2500000000 : ℝ)] ![(7952221007499/25000000000000 : ℝ), (8523889635089/25000000000000 : ℝ), (17047778711569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086963361/5000000000 : ℝ)|^4317 ≤ (7952221007499/25000000000000 : ℝ)^3293
        have hw : |(2086963361/5000000000 : ℝ)|=(2086963361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200456137/5000000000 : ℝ)|^4317 ≤ (8523889635089/25000000000000 : ℝ)^3293
        have hw : |(2200456137/5000000000 : ℝ)|=(2200456137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100228041/2500000000 : ℝ)|^4317 ≤ (17047778711569/50000000000000 : ℝ)^3293
        have hw : |(1100228041/2500000000 : ℝ)|=(1100228041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_8 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129538401/10000000000 : ℝ)*x 0 + (2589885877/5000000000 : ℝ)*x 1 + (1080665093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129538401/10000000000 : ℝ)^4317 ≤ (2632918065837/20000000000000 : ℝ)^3293 := by
    have hnat : (2129538401 : ℕ)^4317*20000000000000^3293 ≤ 2632918065837^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129538401 10000000000 2632918065837 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589885877/5000000000 : ℝ)^4317 ≤ (8443099230843/20000000000000 : ℝ)^3293 := by
    have hnat : (2589885877 : ℕ)^4317*20000000000000^3293 ≤ 8443099230843^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589885877 5000000000 8443099230843 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080665093/2000000000 : ℝ)^4317 ≤ (8923982700613/20000000000000 : ℝ)^3293 := by
    have hnat : (1080665093 : ℕ)^4317*20000000000000^3293 ≤ 8923982700613^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080665093 2000000000 8923982700613 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129538401/10000000000 : ℝ), (2589885877/5000000000 : ℝ), (1080665093/2000000000 : ℝ)] ![(2632918065837/20000000000000 : ℝ), (8443099230843/20000000000000 : ℝ), (8923982700613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129538401/10000000000 : ℝ)|^4317 ≤ (2632918065837/20000000000000 : ℝ)^3293
        have hw : |(-2129538401/10000000000 : ℝ)|=(2129538401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589885877/5000000000 : ℝ)|^4317 ≤ (8443099230843/20000000000000 : ℝ)^3293
        have hw : |(2589885877/5000000000 : ℝ)|=(2589885877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080665093/2000000000 : ℝ)|^4317 ≤ (8923982700613/20000000000000 : ℝ)^3293
        have hw : |(1080665093/2000000000 : ℝ)|=(1080665093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_9 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275521133/10000000000 : ℝ)*x 0 + (-250216741/1250000000 : ℝ)*x 1 + (5403325489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275521133/10000000000 : ℝ)^4317 ≤ (21620726076979/50000000000000 : ℝ)^3293 := by
    have hnat : (5275521133 : ℕ)^4317*50000000000000^3293 ≤ 21620726076979^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275521133 10000000000 21620726076979 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250216741/1250000000 : ℝ)^4317 ≤ (12138634057861/100000000000000 : ℝ)^3293 := by
    have hnat : (250216741 : ℕ)^4317*100000000000000^3293 ≤ 12138634057861^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250216741 1250000000 12138634057861 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403325489/10000000000 : ℝ)^4317 ≤ (44619913762883/100000000000000 : ℝ)^3293 := by
    have hnat : (5403325489 : ℕ)^4317*100000000000000^3293 ≤ 44619913762883^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403325489 10000000000 44619913762883 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275521133/10000000000 : ℝ), (-250216741/1250000000 : ℝ), (5403325489/10000000000 : ℝ)] ![(21620726076979/50000000000000 : ℝ), (12138634057861/100000000000000 : ℝ), (44619913762883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275521133/10000000000 : ℝ)|^4317 ≤ (21620726076979/50000000000000 : ℝ)^3293
        have hw : |(5275521133/10000000000 : ℝ)|=(5275521133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250216741/1250000000 : ℝ)|^4317 ≤ (12138634057861/100000000000000 : ℝ)^3293
        have hw : |(-250216741/1250000000 : ℝ)|=(250216741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403325489/10000000000 : ℝ)|^4317 ≤ (44619913762883/100000000000000 : ℝ)^3293
        have hw : |(5403325489/10000000000 : ℝ)|=(5403325489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_10 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131888031/250000000 : ℝ)*x 0 + (2701662697/5000000000 : ℝ)*x 1 + (-1000866957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131888031/250000000 : ℝ)^4317 ≤ (43241453303723/100000000000000 : ℝ)^3293 := by
    have hnat : (131888031 : ℕ)^4317*100000000000000^3293 ≤ 43241453303723^3293*250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131888031 250000000 43241453303723 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701662697/5000000000 : ℝ)^4317 ≤ (44619912734437/100000000000000 : ℝ)^3293 := by
    have hnat : (2701662697 : ℕ)^4317*100000000000000^3293 ≤ 44619912734437^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701662697 5000000000 44619912734437 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000866957/5000000000 : ℝ)^4317 ≤ (2427726789313/20000000000000 : ℝ)^3293 := by
    have hnat : (1000866957 : ℕ)^4317*20000000000000^3293 ≤ 2427726789313^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000866957 5000000000 2427726789313 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131888031/250000000 : ℝ), (2701662697/5000000000 : ℝ), (-1000866957/5000000000 : ℝ)] ![(43241453303723/100000000000000 : ℝ), (44619912734437/100000000000000 : ℝ), (2427726789313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131888031/250000000 : ℝ)|^4317 ≤ (43241453303723/100000000000000 : ℝ)^3293
        have hw : |(131888031/250000000 : ℝ)|=(131888031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701662697/5000000000 : ℝ)|^4317 ≤ (44619912734437/100000000000000 : ℝ)^3293
        have hw : |(2701662697/5000000000 : ℝ)|=(2701662697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000866957/5000000000 : ℝ)|^4317 ≤ (2427726789313/20000000000000 : ℝ)^3293
        have hw : |(-1000866957/5000000000 : ℝ)|=(1000866957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_11 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2251750739/5000000000 : ℝ)*x 0 + (211794521/500000000 : ℝ)*x 1 + (2117945339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251750739/5000000000 : ℝ)^4317 ≤ (702825308883/2000000000000 : ℝ)^3293 := by
    have hnat : (2251750739 : ℕ)^4317*2000000000000^3293 ≤ 702825308883^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251750739 5000000000 702825308883 2000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211794521/500000000 : ℝ)^4317 ≤ (16214682986453/50000000000000 : ℝ)^3293 := by
    have hnat : (211794521 : ℕ)^4317*50000000000000^3293 ≤ 16214682986453^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211794521 500000000 16214682986453 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117945339/5000000000 : ℝ)^4317 ≤ (16214684281167/50000000000000 : ℝ)^3293 := by
    have hnat : (2117945339 : ℕ)^4317*50000000000000^3293 ≤ 16214684281167^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117945339 5000000000 16214684281167 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251750739/5000000000 : ℝ), (211794521/500000000 : ℝ), (2117945339/5000000000 : ℝ)] ![(702825308883/2000000000000 : ℝ), (16214682986453/50000000000000 : ℝ), (16214684281167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251750739/5000000000 : ℝ)|^4317 ≤ (702825308883/2000000000000 : ℝ)^3293
        have hw : |(2251750739/5000000000 : ℝ)|=(2251750739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211794521/500000000 : ℝ)|^4317 ≤ (16214682986453/50000000000000 : ℝ)^3293
        have hw : |(211794521/500000000 : ℝ)|=(211794521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117945339/5000000000 : ℝ)|^4317 ≤ (16214684281167/50000000000000 : ℝ)^3293
        have hw : |(2117945339/5000000000 : ℝ)|=(2117945339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_12 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77427417/400000000 : ℝ)*x 0 + (171019339/312500000 : ℝ)*x 1 + (5254169497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77427417/400000000 : ℝ)^4317 ≤ (726017438027/6250000000000 : ℝ)^3293 := by
    have hnat : (77427417 : ℕ)^4317*6250000000000^3293 ≤ 726017438027^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77427417 400000000 726017438027 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171019339/312500000 : ℝ)^4317 ≤ (11342889393351/25000000000000 : ℝ)^3293 := by
    have hnat : (171019339 : ℕ)^4317*25000000000000^3293 ≤ 11342889393351^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171019339 312500000 11342889393351 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254169497/10000000000 : ℝ)^4317 ≤ (43012163405099/100000000000000 : ℝ)^3293 := by
    have hnat : (5254169497 : ℕ)^4317*100000000000000^3293 ≤ 43012163405099^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254169497 10000000000 43012163405099 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77427417/400000000 : ℝ), (171019339/312500000 : ℝ), (5254169497/10000000000 : ℝ)] ![(726017438027/6250000000000 : ℝ), (11342889393351/25000000000000 : ℝ), (43012163405099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77427417/400000000 : ℝ)|^4317 ≤ (726017438027/6250000000000 : ℝ)^3293
        have hw : |(-77427417/400000000 : ℝ)|=(77427417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171019339/312500000 : ℝ)|^4317 ≤ (11342889393351/25000000000000 : ℝ)^3293
        have hw : |(171019339/312500000 : ℝ)|=(171019339/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254169497/10000000000 : ℝ)|^4317 ≤ (43012163405099/100000000000000 : ℝ)^3293
        have hw : |(5254169497/10000000000 : ℝ)|=(5254169497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_13 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380223027/10000000000 : ℝ)*x 0 + (-2061738861/10000000000 : ℝ)*x 1 + (262708433/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380223027/10000000000 : ℝ)^4317 ≤ (44369978755263/100000000000000 : ℝ)^3293 := by
    have hnat : (5380223027 : ℕ)^4317*100000000000000^3293 ≤ 44369978755263^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380223027 10000000000 44369978755263 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061738861/10000000000 : ℝ)^4317 ≤ (12617866811333/100000000000000 : ℝ)^3293 := by
    have hnat : (2061738861 : ℕ)^4317*100000000000000^3293 ≤ 12617866811333^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061738861 10000000000 12617866811333 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262708433/500000000 : ℝ)^4317 ≤ (537651930281/1250000000000 : ℝ)^3293 := by
    have hnat : (262708433 : ℕ)^4317*1250000000000^3293 ≤ 537651930281^3293*500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262708433 500000000 537651930281 1250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380223027/10000000000 : ℝ), (-2061738861/10000000000 : ℝ), (262708433/500000000 : ℝ)] ![(44369978755263/100000000000000 : ℝ), (12617866811333/100000000000000 : ℝ), (537651930281/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380223027/10000000000 : ℝ)|^4317 ≤ (44369978755263/100000000000000 : ℝ)^3293
        have hw : |(5380223027/10000000000 : ℝ)|=(5380223027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061738861/10000000000 : ℝ)|^4317 ≤ (12617866811333/100000000000000 : ℝ)^3293
        have hw : |(-2061738861/10000000000 : ℝ)|=(2061738861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262708433/500000000 : ℝ)|^4317 ≤ (537651930281/1250000000000 : ℝ)^3293
        have hw : |(262708433/500000000 : ℝ)|=(262708433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_14 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336263863/625000000 : ℝ)*x 0 + (52541699/100000000 : ℝ)*x 1 + (-515434711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336263863/625000000 : ℝ)^4317 ≤ (5546245697031/12500000000000 : ℝ)^3293 := by
    have hnat : (336263863 : ℕ)^4317*12500000000000^3293 ≤ 5546245697031^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336263863 625000000 5546245697031 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52541699/100000000 : ℝ)^4317 ≤ (2688260483129/6250000000000 : ℝ)^3293 := by
    have hnat : (52541699 : ℕ)^4317*6250000000000^3293 ≤ 2688260483129^3293*100000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52541699 100000000 2688260483129 6250000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515434711/2500000000 : ℝ)^4317 ≤ (12617866674941/100000000000000 : ℝ)^3293 := by
    have hnat : (515434711 : ℕ)^4317*100000000000000^3293 ≤ 12617866674941^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515434711 2500000000 12617866674941 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336263863/625000000 : ℝ), (52541699/100000000 : ℝ), (-515434711/2500000000 : ℝ)] ![(5546245697031/12500000000000 : ℝ), (2688260483129/6250000000000 : ℝ), (12617866674941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336263863/625000000 : ℝ)|^4317 ≤ (5546245697031/12500000000000 : ℝ)^3293
        have hw : |(336263863/625000000 : ℝ)|=(336263863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52541699/100000000 : ℝ)|^4317 ≤ (2688260483129/6250000000000 : ℝ)^3293
        have hw : |(52541699/100000000 : ℝ)|=(52541699/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515434711/2500000000 : ℝ)|^4317 ≤ (12617866674941/100000000000000 : ℝ)^3293
        have hw : |(-515434711/2500000000 : ℝ)|=(515434711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_box_15 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4146983681/10000000000 : ℝ)*x 0 + (882828893/2000000000 : ℝ)*x 1 + (176565759/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146983681/10000000000 : ℝ)^4317 ≤ (15769987991821/50000000000000 : ℝ)^3293 := by
    have hnat : (4146983681 : ℕ)^4317*50000000000000^3293 ≤ 15769987991821^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146983681 10000000000 15769987991821 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882828893/2000000000 : ℝ)^4317 ≤ (3423001448717/10000000000000 : ℝ)^3293 := by
    have hnat : (882828893 : ℕ)^4317*10000000000000^3293 ≤ 3423001448717^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882828893 2000000000 3423001448717 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176565759/400000000 : ℝ)^4317 ≤ (34230009505821/100000000000000 : ℝ)^3293 := by
    have hnat : (176565759 : ℕ)^4317*100000000000000^3293 ≤ 34230009505821^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176565759 400000000 34230009505821 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146983681/10000000000 : ℝ), (882828893/2000000000 : ℝ), (176565759/400000000 : ℝ)] ![(15769987991821/50000000000000 : ℝ), (3423001448717/10000000000000 : ℝ), (34230009505821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146983681/10000000000 : ℝ)|^4317 ≤ (15769987991821/50000000000000 : ℝ)^3293
        have hw : |(4146983681/10000000000 : ℝ)|=(4146983681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882828893/2000000000 : ℝ)|^4317 ≤ (3423001448717/10000000000000 : ℝ)^3293
        have hw : |(882828893/2000000000 : ℝ)|=(882828893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176565759/400000000 : ℝ)|^4317 ≤ (34230009505821/100000000000000 : ℝ)^3293
        have hw : |(176565759/400000000 : ℝ)|=(176565759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62861/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5897/10000 : ℝ) ∧ (40021/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8441/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2237/20000 : ℝ) ^ (1079/256 : ℝ) ≤ (9775733236146429/100000000000000000000 : ℝ) := by
    have hpowers : (2237/20000 : ℝ)^1079 ≤ (9775733236146429/100000000000000000000 : ℝ)^256 := by
      have hnat : (2237 : ℕ)^1079*100000000000000000000^256 ≤ 9775733236146429^256*20000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2237 20000 9775733236146429 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2237/20000 : ℝ)) (X := (9775733236146429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (485494124074637/1562500000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^1079 ≤ (485494124074637/1562500000000000000 : ℝ)^256 := by
      have hnat : (3679 : ℕ)^1079*1562500000000000000^256 ≤ 485494124074637^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 485494124074637 1562500000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (485494124074637/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009775733236146429/50000000000000000000 : ℝ) ≤ (312514494909219/312500000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50009775733236146429/50000000000000000000 : ℝ)^256 ≤ (312514494909219/312500000000000 : ℝ)^1079 := by
      have hnat : (50009775733236146429 : ℕ)^256*312500000000000^1079 ≤ 312514494909219^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009775733236146429 50000000000000000000 312514494909219 312500000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312514494909219/312500000000000 : ℝ)) (X := (50009775733236146429/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040847357176923197/100000000000000000000 : ℝ) ≤ (2000193796011977/2000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (100040847357176923197/100000000000000000000 : ℝ)^256 ≤ (2000193796011977/2000000000000000 : ℝ)^1079 := by
      have hnat : (100040847357176923197 : ℕ)^256*2000000000000000^1079 ≤ 2000193796011977^1079*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040847357176923197 100000000000000000000 2000193796011977 2000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000193796011977/2000000000000000 : ℝ)) (X := (100040847357176923197/100000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (781735494124074637/781250000000000000 : ℝ) ≤ (5000737061512381/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (781735494124074637/781250000000000000 : ℝ)^256 ≤ (5000737061512381/5000000000000000 : ℝ)^1079 := by
      have hnat : (781735494124074637 : ℕ)^256*5000000000000000^1079 ≤ 5000737061512381^1079*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781735494124074637 781250000000000000 5000737061512381 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000737061512381/5000000000000000 : ℝ)) (X := (781735494124074637/781250000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9775733236146429/100000000000000000000 : ℝ) ≤ ((17650168880329087379/17655000000000000000 : ℝ)+2*(505142964877/353100000000000 : ℝ)*(2237/20000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17650168880329087379/17655000000000000000 : ℝ)+2*(505142964877/353100000000000 : ℝ)*(2237/20000 : ℝ)=(312514494909219/312500000000000 : ℝ) by norm_num, show 1+2*(9775733236146429/100000000000000000000 : ℝ)=(50009775733236146429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(485494124074637/1562500000000000000 : ℝ)+(9775733236146429/100000000000000000000 : ℝ) ≤ ((17650168880329087379/17655000000000000000 : ℝ)+(505142964877/353100000000000 : ℝ)*((3679/25000 : ℝ)+(2237/20000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (17650168880329087379/17655000000000000000 : ℝ)+(505142964877/353100000000000 : ℝ)*((3679/25000 : ℝ)+(2237/20000 : ℝ))=(2000193796011977/2000000000000000 : ℝ) by norm_num, show 1+(485494124074637/1562500000000000000 : ℝ)+(9775733236146429/100000000000000000000 : ℝ)=(100040847357176923197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(485494124074637/1562500000000000000 : ℝ) ≤ ((17650168880329087379/17655000000000000000 : ℝ)+2*(505142964877/353100000000000 : ℝ)*(3679/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (17650168880329087379/17655000000000000000 : ℝ)+2*(505142964877/353100000000000 : ℝ)*(3679/25000 : ℝ)=(5000737061512381/5000000000000000 : ℝ) by norm_num, show 1+2*(485494124074637/1562500000000000000 : ℝ)=(781735494124074637/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17650168880329087379/17655000000000000000 : ℝ)*(X 1 0+X 2 0)+(505142964877/353100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (17650168880329087379/17655000000000000000 : ℝ)) (alpha := (505142964877/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17650168880329087379/17655000000000000000 : ℝ)*(X 0 1+X 2 1)+(505142964877/353100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (17650168880329087379/17655000000000000000 : ℝ)) (alpha := (505142964877/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17650168880329087379/17655000000000000000 : ℝ)*(X 0 2+X 1 2)+(505142964877/353100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (17650168880329087379/17655000000000000000 : ℝ)) (alpha := (505142964877/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-186501167/1000000000 : ℝ)*X 0 0+(336832003/625000000 : ℝ)*X 0 1+(1347328183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528536299/1000000000 : ℝ)*X 1 0+(-501875001/2500000000 : ℝ)*X 1 1+(5389311991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285362793/10000000000 : ℝ)*X 2 0+(5389312189/10000000000 : ℝ)*X 2 1+(-803/4000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4470555887/10000000000 : ℝ)*X 0 0+(531581323/1250000000 : ℝ)*X 0 1+(1063162719/2500000000 : ℝ)*X 0 2+(4470555887/10000000000 : ℝ)*X 1 0+(531581323/1250000000 : ℝ)*X 1 1+(1063162719/2500000000 : ℝ)*X 1 2+(4470555887/10000000000 : ℝ)*X 2 0+(531581323/1250000000 : ℝ)*X 2 1+(1063162719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2199904529/10000000000 : ℝ)*X 0 0+(5265249449/10000000000 : ℝ)*X 0 1+(329078177/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268622303/500000000 : ℝ)*X 1 0+(-257173299/1250000000 : ℝ)*X 1 1+(1053050117/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074489077/2000000000 : ℝ)*X 2 0+(658156409/1250000000 : ℝ)*X 2 1+(-2057386381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086963361/5000000000 : ℝ)*X 0 0+(2200456137/5000000000 : ℝ)*X 0 1+(1100228041/2500000000 : ℝ)*X 0 2+(2086963361/5000000000 : ℝ)*X 1 0+(2200456137/5000000000 : ℝ)*X 1 1+(1100228041/2500000000 : ℝ)*X 1 2+(2086963361/5000000000 : ℝ)*X 2 0+(2200456137/5000000000 : ℝ)*X 2 1+(1100228041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2129538401/10000000000 : ℝ)*X 0 0+(2589885877/5000000000 : ℝ)*X 0 1+(1080665093/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275521133/10000000000 : ℝ)*X 1 0+(-250216741/1250000000 : ℝ)*X 1 1+(5403325489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((131888031/250000000 : ℝ)*X 2 0+(2701662697/5000000000 : ℝ)*X 2 1+(-1000866957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251750739/5000000000 : ℝ)*X 0 0+(211794521/500000000 : ℝ)*X 0 1+(2117945339/5000000000 : ℝ)*X 0 2+(2251750739/5000000000 : ℝ)*X 1 0+(211794521/500000000 : ℝ)*X 1 1+(2117945339/5000000000 : ℝ)*X 1 2+(2251750739/5000000000 : ℝ)*X 2 0+(211794521/500000000 : ℝ)*X 2 1+(2117945339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-77427417/400000000 : ℝ)*X 0 0+(171019339/312500000 : ℝ)*X 0 1+(5254169497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380223027/10000000000 : ℝ)*X 1 0+(-2061738861/10000000000 : ℝ)*X 1 1+(262708433/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336263863/625000000 : ℝ)*X 2 0+(52541699/100000000 : ℝ)*X 2 1+(-515434711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4146983681/10000000000 : ℝ)*X 0 0+(882828893/2000000000 : ℝ)*X 0 1+(176565759/400000000 : ℝ)*X 0 2+(4146983681/10000000000 : ℝ)*X 1 0+(882828893/2000000000 : ℝ)*X 1 1+(176565759/400000000 : ℝ)*X 1 2+(4146983681/10000000000 : ℝ)*X 2 0+(882828893/2000000000 : ℝ)*X 2 1+(176565759/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62861/100000 : ℝ) ≤ (-184962578405518350793538526108221/294250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80979349/50000000000000 : ℝ)*(upper1) + (180634091/100000000000000 : ℝ)*(lower4) + (47683183/50000000000000 : ℝ)*(upper5) + (2937434782863601/100000000000000 : ℝ)*(major0) + (2937434782863601/100000000000000 : ℝ)*(major1) + (2937434782863601/100000000000000 : ℝ)*(major2) + (1334588909/12500000000000 : ℝ)*(sp3) + (4004587193505383/100000000000000 : ℝ)*(sp4) + (80090606094971/2000000000000 : ℝ)*(sp5) + (4004414980368879/100000000000000 : ℝ)*(sp6) + (945602187347127/50000000000000 : ℝ)*(sp7) + (10158760199/50000000000000 : ℝ)*(sp12) + (7720627723/10000000000000 : ℝ)*(sp13) + (96265328451/50000000000000 : ℝ)*(sp14) + (945607525702763/50000000000000 : ℝ)*(f.failure) + (4004607511025781/100000000000000 : ℝ)*(f.sum) + (1591289792713/4413750000000000000000000000 : ℝ)*base65 + (5691394452738941779/1765500000000000000000000000000000 : ℝ)*base67 + (6149472378873558221/1765500000000000000000000000000000 : ℝ)*base70 + (1914202903689558221/1765500000000000000000000000000000 : ℝ)*base72 + (88973700075907/17655000000000000000000000000 : ℝ)*base73 + (1585385998262441779/1765500000000000000000000000000000 : ℝ)*base75 + (8547723152765058221/1765500000000000000000000000000000 : ℝ)*base78 + (8363871837474558221/1765500000000000000000000000000000 : ℝ)*base80 + (3310517902361/8827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7996451/5000000000000000000000 : ℝ)*base89 + (7996451/5000000000000000000000 : ℝ)*base91 + (7996451/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5897/10000 : ℝ) ≤ (173527700645656117736780601457143/294250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2803403/100000000000000 : ℝ)*(lower0) + (802459/781250000000 : ℝ)*(lower1) + (2195841/10000000000000 : ℝ)*(lower3) + (22111397/20000000000000 : ℝ)*(lower5) + (3006620018347683/100000000000000 : ℝ)*(major0) + (3006620018347683/100000000000000 : ℝ)*(major1) + (3006620018347683/100000000000000 : ℝ)*(major2) + (4057803874651939/100000000000000 : ℝ)*(sp0) + (4057742453604139/100000000000000 : ℝ)*(sp1) + (1014455919306143/25000000000000 : ℝ)*(sp2) + (96787498958449/5000000000000 : ℝ)*(sp3) + (8753494033/100000000000000 : ℝ)*(sp7) + (81223620433/100000000000000 : ℝ)*(sp9) + (19802572633/100000000000000 : ℝ)*(sp12) + (1935758732663013/100000000000000 : ℝ)*(f.failure) + (1014455919306143/25000000000000 : ℝ)*(f.sum) + (328297905531/2942500000000000000000000000 : ℝ)*base65 + (1018868350343247619/588500000000000000000000000000000 : ℝ)*base67 + (2417607133207747619/588500000000000000000000000000000 : ℝ)*base69 + (1681092007086252381/588500000000000000000000000000000 : ℝ)*base72 + (78502522185927/5885000000000000000000000000 : ℝ)*base73 + (297310816816752381/588500000000000000000000000000000 : ℝ)*base76 + (2491006123779247619/588500000000000000000000000000000 : ℝ)*base77 + (627009592041247619/588500000000000000000000000000000 : ℝ)*base79 + (23484915694423/5885000000000000000000000000 : ℝ)*base82 + (27910701/10000000000000000000000 : ℝ)*base89 + (27910701/10000000000000000000000 : ℝ)*base91 + (27910701/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40021/50000 : ℝ) ≤ (29441269390651351530057894714611/36781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086347/6250000000000 : ℝ)*(upper0) + (12227553/100000000000000 : ℝ)*(lower1) + (56826789/100000000000000 : ℝ)*(lower3) + (5094583/100000000000000 : ℝ)*(upper4) + (829521918924191/25000000000000 : ℝ)*(major0) + (829521918924191/25000000000000 : ℝ)*(major1) + (829521918924191/25000000000000 : ℝ)*(major2) + (3969249911/100000000000000 : ℝ)*(sp0) + (21727953523/50000000000000 : ℝ)*(sp1) + (5929546329/25000000000000 : ℝ)*(sp3) + (223659916823989/5000000000000 : ℝ)*(sp8) + (1118289712455661/25000000000000 : ℝ)*(sp9) + (447320230572969/10000000000000 : ℝ)*(sp10) + (1068133958266291/50000000000000 : ℝ)*(sp11) + (2136291634717899/100000000000000 : ℝ)*(f.failure) + (447320230572969/10000000000000 : ℝ)*(f.sum) + (7371743099681/8827500000000000000000000000 : ℝ)*base66 + (862836126017235389/441375000000000000000000000000000 : ℝ)*base67 + (372405276119264611/441375000000000000000000000000000 : ℝ)*base70 + (471943900106235389/441375000000000000000000000000000 : ℝ)*base71 + (13828873466747/4413750000000000000000000000 : ℝ)*base73 + (7276624820074485389/441375000000000000000000000000000 : ℝ)*base75 + (3225659393525235389/441375000000000000000000000000000 : ℝ)*base77 + (6792538874970735389/441375000000000000000000000000000 : ℝ)*base79 + (5425195367/4413750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (74168323/10000000000000000000000 : ℝ)*base89 + (74168323/10000000000000000000000 : ℝ)*base91 + (74168323/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-8441/10000 : ℝ) ≤ (-24837015665087417035747792356621/29425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253666431/100000000000000 : ℝ)*(lower0) + (144547/6250000000000 : ℝ)*(lower1) + (16515847/12500000000000 : ℝ)*(lower2) + (416224081/100000000000000 : ℝ)*(lower4) + (335473616354667/10000000000000 : ℝ)*(major0) + (335473616354667/10000000000000 : ℝ)*(major1) + (335473616354667/10000000000000 : ℝ)*(major2) + (878759167/20000000000000 : ℝ)*(sp4) + (352228450513/100000000000000 : ℝ)*(sp5) + (131717260689/100000000000000 : ℝ)*(sp7) + (915543355836547/20000000000000 : ℝ)*(sp12) + (572171118066007/12500000000000 : ℝ)*(sp13) + (4577721172978569/100000000000000 : ℝ)*(sp14) + (2159755393427379/100000000000000 : ℝ)*(sp15) + (539971777672017/25000000000000 : ℝ)*(f.failure) + (4577721172978569/100000000000000 : ℝ)*(f.sum) + (15777783905353/1177000000000000000000000000 : ℝ)*base66 + (526495233863134069/58850000000000000000000000000000 : ℝ)*base68 + (633184005745134069/58850000000000000000000000000000 : ℝ)*base70 + (1523965636765184069/58850000000000000000000000000000 : ℝ)*base72 + (866595352813/1177000000000000000000000000 : ℝ)*base73 + (682900841787634069/58850000000000000000000000000000 : ℝ)*base76 + (125681307136184069/58850000000000000000000000000000 : ℝ)*base78 + (40125813422384069/58850000000000000000000000000000 : ℝ)*base80 + (6768224154139/1177000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (43983609/2500000000000000000000 : ℝ)*base89 + (43983609/2500000000000000000000 : ℝ)*base91 + (43983609/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1357_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5897/10000 : ℝ) else (40021/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8441/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1357_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1357_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5897/10000 : ℝ) else (40021/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8441/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1357_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5897/10000 : ℝ) else (40021/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8441/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
