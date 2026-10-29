-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1576_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:11.093452+00:00
-- url     : https://prove2.me/submissions/30ce070b-f441-4f62-ae28-8dd8d20758aa

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
theorem support_rectangle_w1576_s3_0 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355443579/2000000000 : ℝ)*x 0 + (542658881/1000000000 : ℝ)*x 1 + (2609428387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355443579/2000000000 : ℝ)^4649 ≤ (2181902551371/20000000000000 : ℝ)^3625 := by
    have hnat : (355443579 : ℕ)^4649*20000000000000^3625 ≤ 2181902551371^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355443579 2000000000 2181902551371 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542658881/1000000000 : ℝ)^4649 ≤ (45659940953849/100000000000000 : ℝ)^3625 := by
    have hnat : (542658881 : ℕ)^4649*100000000000000^3625 ≤ 45659940953849^3625*1000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542658881 1000000000 45659940953849 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609428387/5000000000 : ℝ)^4649 ≤ (8686109255171/20000000000000 : ℝ)^3625 := by
    have hnat : (2609428387 : ℕ)^4649*20000000000000^3625 ≤ 8686109255171^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609428387 5000000000 8686109255171 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355443579/2000000000 : ℝ), (542658881/1000000000 : ℝ), (2609428387/5000000000 : ℝ)] ![(2181902551371/20000000000000 : ℝ), (45659940953849/100000000000000 : ℝ), (8686109255171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355443579/2000000000 : ℝ)|^4649 ≤ (2181902551371/20000000000000 : ℝ)^3625
        have hw : |(-355443579/2000000000 : ℝ)|=(355443579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542658881/1000000000 : ℝ)|^4649 ≤ (45659940953849/100000000000000 : ℝ)^3625
        have hw : |(542658881/1000000000 : ℝ)|=(542658881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609428387/5000000000 : ℝ)|^4649 ≤ (8686109255171/20000000000000 : ℝ)^3625
        have hw : |(2609428387/5000000000 : ℝ)|=(2609428387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_1 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674117079/5000000000 : ℝ)*x 0 + (-235439221/1250000000 : ℝ)*x 1 + (5218856743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674117079/5000000000 : ℝ)^4649 ≤ (44816149604481/100000000000000 : ℝ)^3625 := by
    have hnat : (2674117079 : ℕ)^4649*100000000000000^3625 ≤ 44816149604481^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674117079 5000000000 44816149604481 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235439221/1250000000 : ℝ)^4649 ≤ (5876652217459/50000000000000 : ℝ)^3625 := by
    have hnat : (235439221 : ℕ)^4649*50000000000000^3625 ≤ 5876652217459^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235439221 1250000000 5876652217459 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218856743/10000000000 : ℝ)^4649 ≤ (43430545945003/100000000000000 : ℝ)^3625 := by
    have hnat : (5218856743 : ℕ)^4649*100000000000000^3625 ≤ 43430545945003^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218856743 10000000000 43430545945003 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674117079/5000000000 : ℝ), (-235439221/1250000000 : ℝ), (5218856743/10000000000 : ℝ)] ![(44816149604481/100000000000000 : ℝ), (5876652217459/50000000000000 : ℝ), (43430545945003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674117079/5000000000 : ℝ)|^4649 ≤ (44816149604481/100000000000000 : ℝ)^3625
        have hw : |(2674117079/5000000000 : ℝ)|=(2674117079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235439221/1250000000 : ℝ)|^4649 ≤ (5876652217459/50000000000000 : ℝ)^3625
        have hw : |(-235439221/1250000000 : ℝ)|=(235439221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218856743/10000000000 : ℝ)|^4649 ≤ (43430545945003/100000000000000 : ℝ)^3625
        have hw : |(5218856743/10000000000 : ℝ)|=(5218856743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_2 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348234127/10000000000 : ℝ)*x 0 + (2609428391/5000000000 : ℝ)*x 1 + (-941756879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348234127/10000000000 : ℝ)^4649 ≤ (44816149271333/100000000000000 : ℝ)^3625 := by
    have hnat : (5348234127 : ℕ)^4649*100000000000000^3625 ≤ 44816149271333^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348234127 10000000000 44816149271333 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609428391/5000000000 : ℝ)^4649 ≤ (10857636590309/25000000000000 : ℝ)^3625 := by
    have hnat : (2609428391 : ℕ)^4649*25000000000000^3625 ≤ 10857636590309^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609428391 5000000000 10857636590309 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941756879/5000000000 : ℝ)^4649 ≤ (1175330435489/10000000000000 : ℝ)^3625 := by
    have hnat : (941756879 : ℕ)^4649*10000000000000^3625 ≤ 1175330435489^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941756879 5000000000 1175330435489 10000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348234127/10000000000 : ℝ), (2609428391/5000000000 : ℝ), (-941756879/5000000000 : ℝ)] ![(44816149271333/100000000000000 : ℝ), (10857636590309/25000000000000 : ℝ), (1175330435489/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348234127/10000000000 : ℝ)|^4649 ≤ (44816149271333/100000000000000 : ℝ)^3625
        have hw : |(5348234127/10000000000 : ℝ)|=(5348234127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609428391/5000000000 : ℝ)|^4649 ≤ (10857636590309/25000000000000 : ℝ)^3625
        have hw : |(2609428391/5000000000 : ℝ)|=(2609428391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941756879/5000000000 : ℝ)|^4649 ≤ (1175330435489/10000000000000 : ℝ)^3625
        have hw : |(-941756879/5000000000 : ℝ)|=(941756879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_3 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530090531/1250000000 : ℝ)*x 0 + (2000149417/5000000000 : ℝ)*x 1 + (4492668217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530090531/1250000000 : ℝ)^4649 ≤ (8320286386329/25000000000000 : ℝ)^3625 := by
    have hnat : (530090531 : ℕ)^4649*25000000000000^3625 ≤ 8320286386329^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530090531 1250000000 8320286386329 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000149417/5000000000 : ℝ)^4649 ≤ (30880932716797/100000000000000 : ℝ)^3625 := by
    have hnat : (2000149417 : ℕ)^4649*100000000000000^3625 ≤ 30880932716797^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000149417 5000000000 30880932716797 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492668217/10000000000 : ℝ)^4649 ≤ (35837921724499/100000000000000 : ℝ)^3625 := by
    have hnat : (4492668217 : ℕ)^4649*100000000000000^3625 ≤ 35837921724499^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492668217 10000000000 35837921724499 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530090531/1250000000 : ℝ), (2000149417/5000000000 : ℝ), (4492668217/10000000000 : ℝ)] ![(8320286386329/25000000000000 : ℝ), (30880932716797/100000000000000 : ℝ), (35837921724499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530090531/1250000000 : ℝ)|^4649 ≤ (8320286386329/25000000000000 : ℝ)^3625
        have hw : |(530090531/1250000000 : ℝ)|=(530090531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000149417/5000000000 : ℝ)|^4649 ≤ (30880932716797/100000000000000 : ℝ)^3625
        have hw : |(2000149417/5000000000 : ℝ)|=(2000149417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492668217/10000000000 : ℝ)|^4649 ≤ (35837921724499/100000000000000 : ℝ)^3625
        have hw : |(4492668217/10000000000 : ℝ)|=(4492668217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_4 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355449137/2000000000 : ℝ)*x 0 + (5219955623/10000000000 : ℝ)*x 1 + (678185209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355449137/2000000000 : ℝ)^4649 ≤ (5454865767949/50000000000000 : ℝ)^3625 := by
    have hnat : (355449137 : ℕ)^4649*50000000000000^3625 ≤ 5454865767949^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355449137 2000000000 5454865767949 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219955623/10000000000 : ℝ)^4649 ≤ (8688454846657/20000000000000 : ℝ)^3625 := by
    have hnat : (5219955623 : ℕ)^4649*20000000000000^3625 ≤ 8688454846657^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219955623 10000000000 8688454846657 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678185209/1250000000 : ℝ)^4649 ≤ (45647994219477/100000000000000 : ℝ)^3625 := by
    have hnat : (678185209 : ℕ)^4649*100000000000000^3625 ≤ 45647994219477^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678185209 1250000000 45647994219477 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355449137/2000000000 : ℝ), (5219955623/10000000000 : ℝ), (678185209/1250000000 : ℝ)] ![(5454865767949/50000000000000 : ℝ), (8688454846657/20000000000000 : ℝ), (45647994219477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355449137/2000000000 : ℝ)|^4649 ≤ (5454865767949/50000000000000 : ℝ)^3625
        have hw : |(-355449137/2000000000 : ℝ)|=(355449137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219955623/10000000000 : ℝ)|^4649 ≤ (8688454846657/20000000000000 : ℝ)^3625
        have hw : |(5219955623/10000000000 : ℝ)|=(5219955623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678185209/1250000000 : ℝ)|^4649 ≤ (45647994219477/100000000000000 : ℝ)^3625
        have hw : |(678185209/1250000000 : ℝ)|=(678185209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_5 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293235457/10000000000 : ℝ)*x 0 + (-335377781/2000000000 : ℝ)*x 1 + (2712740813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293235457/10000000000 : ℝ)^4649 ≤ (22112977468671/50000000000000 : ℝ)^3625 := by
    have hnat : (5293235457 : ℕ)^4649*50000000000000^3625 ≤ 22112977468671^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293235457 10000000000 22112977468671 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335377781/2000000000 : ℝ)^4649 ≤ (1265756415141/12500000000000 : ℝ)^3625 := by
    have hnat : (335377781 : ℕ)^4649*12500000000000^3625 ≤ 1265756415141^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335377781 2000000000 1265756415141 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712740813/5000000000 : ℝ)^4649 ≤ (45647993723121/100000000000000 : ℝ)^3625 := by
    have hnat : (2712740813 : ℕ)^4649*100000000000000^3625 ≤ 45647993723121^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712740813 5000000000 45647993723121 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293235457/10000000000 : ℝ), (-335377781/2000000000 : ℝ), (2712740813/5000000000 : ℝ)] ![(22112977468671/50000000000000 : ℝ), (1265756415141/12500000000000 : ℝ), (45647993723121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293235457/10000000000 : ℝ)|^4649 ≤ (22112977468671/50000000000000 : ℝ)^3625
        have hw : |(5293235457/10000000000 : ℝ)|=(5293235457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335377781/2000000000 : ℝ)|^4649 ≤ (1265756415141/12500000000000 : ℝ)^3625
        have hw : |(-335377781/2000000000 : ℝ)|=(335377781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712740813/5000000000 : ℝ)|^4649 ≤ (45647993723121/100000000000000 : ℝ)^3625
        have hw : |(2712740813/5000000000 : ℝ)|=(2712740813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_6 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293235493/10000000000 : ℝ)*x 0 + (2712740841/5000000000 : ℝ)*x 1 + (-1676888777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293235493/10000000000 : ℝ)^4649 ≤ (8845191064619/20000000000000 : ℝ)^3625 := by
    have hnat : (5293235493 : ℕ)^4649*20000000000000^3625 ≤ 8845191064619^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293235493 10000000000 8845191064619 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712740841/5000000000 : ℝ)^4649 ≤ (2282399716369/5000000000000 : ℝ)^3625 := by
    have hnat : (2712740841 : ℕ)^4649*5000000000000^3625 ≤ 2282399716369^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712740841 5000000000 2282399716369 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676888777/10000000000 : ℝ)^4649 ≤ (5063025164923/50000000000000 : ℝ)^3625 := by
    have hnat : (1676888777 : ℕ)^4649*50000000000000^3625 ≤ 5063025164923^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676888777 10000000000 5063025164923 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293235493/10000000000 : ℝ), (2712740841/5000000000 : ℝ), (-1676888777/10000000000 : ℝ)] ![(8845191064619/20000000000000 : ℝ), (2282399716369/5000000000000 : ℝ), (5063025164923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293235493/10000000000 : ℝ)|^4649 ≤ (8845191064619/20000000000000 : ℝ)^3625
        have hw : |(5293235493/10000000000 : ℝ)|=(5293235493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712740841/5000000000 : ℝ)|^4649 ≤ (2282399716369/5000000000000 : ℝ)^3625
        have hw : |(2712740841/5000000000 : ℝ)|=(2712740841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676888777/10000000000 : ℝ)|^4649 ≤ (5063025164923/50000000000000 : ℝ)^3625
        have hw : |(-1676888777/10000000000 : ℝ)|=(1676888777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s3_7 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060197463/2500000000 : ℝ)*x 0 + (89801269/200000000 : ℝ)*x 1 + (1000730817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060197463/2500000000 : ℝ)^4649 ≤ (832045146123/2500000000000 : ℝ)^3625 := by
    have hnat : (1060197463 : ℕ)^4649*2500000000000^3625 ≤ 832045146123^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060197463 2500000000 832045146123 2500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89801269/200000000 : ℝ)^4649 ≤ (35811276258781/100000000000000 : ℝ)^3625 := by
    have hnat : (89801269 : ℕ)^4649*100000000000000^3625 ≤ 35811276258781^3625*200000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89801269 200000000 35811276258781 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000730817/2500000000 : ℝ)^4649 ≤ (15453458938511/50000000000000 : ℝ)^3625 := by
    have hnat : (1000730817 : ℕ)^4649*50000000000000^3625 ≤ 15453458938511^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000730817 2500000000 15453458938511 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060197463/2500000000 : ℝ), (89801269/200000000 : ℝ), (1000730817/2500000000 : ℝ)] ![(832045146123/2500000000000 : ℝ), (35811276258781/100000000000000 : ℝ), (15453458938511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060197463/2500000000 : ℝ)|^4649 ≤ (832045146123/2500000000000 : ℝ)^3625
        have hw : |(1060197463/2500000000 : ℝ)|=(1060197463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89801269/200000000 : ℝ)|^4649 ≤ (35811276258781/100000000000000 : ℝ)^3625
        have hw : |(89801269/200000000 : ℝ)|=(89801269/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000730817/2500000000 : ℝ)|^4649 ≤ (15453458938511/50000000000000 : ℝ)^3625
        have hw : |(1000730817/2500000000 : ℝ)|=(1000730817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1576_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1111/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15517/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3949/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3949/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3949/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3949/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3949/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3949/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10853/100000 : ℝ) ^ (4647/1024 : ℝ) ≤ (4199930691692919/100000000000000000000 : ℝ) := by
    have hpowers : (10853/100000 : ℝ)^4647 ≤ (4199930691692919/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10853 : ℕ)^4647*100000000000000000000^1024 ≤ 4199930691692919^1024*100000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10853 100000 4199930691692919 100000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10853/100000 : ℝ)) (X := (4199930691692919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3949/25000 : ℝ) ^ (4647/1024 : ℝ) ≤ (11532088935846411/50000000000000000000 : ℝ) := by
    have hpowers : (3949/25000 : ℝ)^4647 ≤ (11532088935846411/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3949 : ℕ)^4647*50000000000000000000^1024 ≤ 11532088935846411^1024*25000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3949 25000 11532088935846411 50000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3949/25000 : ℝ)) (X := (11532088935846411/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004199930691692919/50000000000000000000 : ℝ) ≤ (5000092545474721/5000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (50004199930691692919/50000000000000000000 : ℝ)^1024 ≤ (5000092545474721/5000000000000000 : ℝ)^4647 := by
      have hnat : (50004199930691692919 : ℕ)^1024*5000000000000000^4647 ≤ 5000092545474721^4647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004199930691692919 50000000000000000000 5000092545474721 5000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000092545474721/5000000000000000 : ℝ)) (X := (50004199930691692919/50000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027264108563385741/100000000000000000000 : ℝ) ≤ (5000300360237133/5000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (100027264108563385741/100000000000000000000 : ℝ)^1024 ≤ (5000300360237133/5000000000000000 : ℝ)^4647 := by
      have hnat : (100027264108563385741 : ℕ)^1024*5000000000000000^4647 ≤ 5000300360237133^4647*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027264108563385741 100000000000000000000 5000300360237133 5000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000300360237133/5000000000000000 : ℝ)) (X := (100027264108563385741/100000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011532088935846411/25000000000000000000 : ℝ) ≤ (1000101634999909/1000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (25011532088935846411/25000000000000000000 : ℝ)^1024 ≤ (1000101634999909/1000000000000000 : ℝ)^4647 := by
      have hnat : (25011532088935846411 : ℕ)^1024*1000000000000000^4647 ≤ 1000101634999909^4647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011532088935846411 25000000000000000000 1000101634999909 1000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000101634999909/1000000000000000 : ℝ)) (X := (25011532088935846411/25000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4199930691692919/100000000000000000000 : ℝ) ≤ ((24710946625048631031/24715000000000000000 : ℝ)+2*(51953690603/61787500000000 : ℝ)*(10853/100000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (24710946625048631031/24715000000000000000 : ℝ)+2*(51953690603/61787500000000 : ℝ)*(10853/100000 : ℝ)=(5000092545474721/5000000000000000 : ℝ) by norm_num, show 1+2*(4199930691692919/100000000000000000000 : ℝ)=(50004199930691692919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11532088935846411/50000000000000000000 : ℝ)+(4199930691692919/100000000000000000000 : ℝ) ≤ ((24710946625048631031/24715000000000000000 : ℝ)+(51953690603/61787500000000 : ℝ)*((3949/25000 : ℝ)+(10853/100000 : ℝ)))^(4647/1024 : ℝ) := by
    rw [show (24710946625048631031/24715000000000000000 : ℝ)+(51953690603/61787500000000 : ℝ)*((3949/25000 : ℝ)+(10853/100000 : ℝ))=(5000300360237133/5000000000000000 : ℝ) by norm_num, show 1+(11532088935846411/50000000000000000000 : ℝ)+(4199930691692919/100000000000000000000 : ℝ)=(100027264108563385741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11532088935846411/50000000000000000000 : ℝ) ≤ ((24710946625048631031/24715000000000000000 : ℝ)+2*(51953690603/61787500000000 : ℝ)*(3949/25000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (24710946625048631031/24715000000000000000 : ℝ)+2*(51953690603/61787500000000 : ℝ)*(3949/25000 : ℝ)=(1000101634999909/1000000000000000 : ℝ) by norm_num, show 1+2*(11532088935846411/50000000000000000000 : ℝ)=(25011532088935846411/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24710946625048631031/24715000000000000000 : ℝ)*(X 1 0+X 2 0)+(51953690603/61787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3949/25000 : ℝ)) (c := (24710946625048631031/24715000000000000000 : ℝ)) (alpha := (51953690603/61787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24710946625048631031/24715000000000000000 : ℝ)*(X 0 1+X 2 1)+(51953690603/61787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3949/25000 : ℝ)) (c := (24710946625048631031/24715000000000000000 : ℝ)) (alpha := (51953690603/61787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24710946625048631031/24715000000000000000 : ℝ)*(X 0 2+X 1 2)+(51953690603/61787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3949/25000 : ℝ)) (c := (24710946625048631031/24715000000000000000 : ℝ)) (alpha := (51953690603/61787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-355443579/2000000000 : ℝ)*X 0 0+(542658881/1000000000 : ℝ)*X 0 1+(2609428387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674117079/5000000000 : ℝ)*X 1 0+(-235439221/1250000000 : ℝ)*X 1 1+(5218856743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348234127/10000000000 : ℝ)*X 2 0+(2609428391/5000000000 : ℝ)*X 2 1+(-941756879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530090531/1250000000 : ℝ)*X 0 0+(2000149417/5000000000 : ℝ)*X 0 1+(4492668217/10000000000 : ℝ)*X 0 2+(530090531/1250000000 : ℝ)*X 1 0+(2000149417/5000000000 : ℝ)*X 1 1+(4492668217/10000000000 : ℝ)*X 1 2+(530090531/1250000000 : ℝ)*X 2 0+(2000149417/5000000000 : ℝ)*X 2 1+(4492668217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-355449137/2000000000 : ℝ)*X 0 0+(5219955623/10000000000 : ℝ)*X 0 1+(678185209/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293235457/10000000000 : ℝ)*X 1 0+(-335377781/2000000000 : ℝ)*X 1 1+(2712740813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293235493/10000000000 : ℝ)*X 2 0+(2712740841/5000000000 : ℝ)*X 2 1+(-1676888777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1060197463/2500000000 : ℝ)*X 0 0+(89801269/200000000 : ℝ)*X 0 1+(1000730817/2500000000 : ℝ)*X 0 2+(1060197463/2500000000 : ℝ)*X 1 0+(89801269/200000000 : ℝ)*X 1 1+(1000730817/2500000000 : ℝ)*X 1 2+(1060197463/2500000000 : ℝ)*X 2 0+(89801269/200000000 : ℝ)*X 2 1+(1000730817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1538194205574157709961976587/123575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2115209497/100000000000000 : ℝ)*(base19) + (1964081923/100000000000000 : ℝ)*(base23) + (8237911/12500000000000 : ℝ)*(lower2) + (149936949/50000000000000 : ℝ)*(upper3) + (108382833/50000000000000 : ℝ)*(upper5) + (684498781566241/20000000000000 : ℝ)*(major0) + (684498781566241/20000000000000 : ℝ)*(major1) + (684498781566241/20000000000000 : ℝ)*(major2) + (4813928769131857/100000000000000 : ℝ)*(sp0) + (1203490090765819/25000000000000 : ℝ)*(sp1) + (96279210283817/2000000000000 : ℝ)*(sp2) + (406201904890983/20000000000000 : ℝ)*(sp3) + (8427285229/25000000000000 : ℝ)*(sp4) + (3849504889/25000000000000 : ℝ)*(sp7) + (2031024922474471/100000000000000 : ℝ)*(f.failure) + (4813962478272773/100000000000000 : ℝ)*(f.sum) + (16131252762533/4943000000000000000000000000 : ℝ)*base65 + (5566735346867424471/494300000000000000000000000000000 : ℝ)*base67 + (6157958538591924471/494300000000000000000000000000000 : ℝ)*base69 + (3236892783991824471/494300000000000000000000000000000 : ℝ)*base71 + (8987453408539/2471500000000000000000000000 : ℝ)*base73 + (4447023516020524471/494300000000000000000000000000000 : ℝ)*base75 + (4451607184141224471/494300000000000000000000000000000 : ℝ)*base77 + (1937012427119175529/494300000000000000000000000000000 : ℝ)*base80 + (768636266943/197720000000000000000000000 : ℝ)*base81 + (2728743/250000000000000000000 : ℝ)*base90 + (2728743/250000000000000000000 : ℝ)*base92 + (2728743/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1281195348378413756647974519/123575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1741335639/100000000000000 : ℝ)*(base19) + (1790226197/100000000000000 : ℝ)*(base23) + (5857/781250000000 : ℝ)*(upper2) + (22384563/12500000000000 : ℝ)*(upper3) + (126808103/50000000000000 : ℝ)*(upper5) + (345918138519683/10000000000000 : ℝ)*(major0) + (345918138519683/10000000000000 : ℝ)*(major1) + (345918138519683/10000000000000 : ℝ)*(major2) + (28801907741/100000000000000 : ℝ)*(sp1) + (15093097269/50000000000000 : ℝ)*(sp2) + (4865565898672531/100000000000000 : ℝ)*(sp4) + (4865535355429151/100000000000000 : ℝ)*(sp5) + (973106784450359/20000000000000 : ℝ)*(sp6) + (1026398263064641/50000000000000 : ℝ)*(sp7) + (1026398263064641/50000000000000 : ℝ)*(f.failure) + (4865565898672531/100000000000000 : ℝ)*(f.sum) + (26155663025737/4943000000000000000000000000 : ℝ)*base65 + (1661590635780266827/247150000000000000000000000000000 : ℝ)*base68 + (1655325555049516827/247150000000000000000000000000000 : ℝ)*base70 + (3505091293217666827/247150000000000000000000000000000 : ℝ)*base72 + (24077983560533/4943000000000000000000000000 : ℝ)*base73 + (1457114655182933173/247150000000000000000000000000000 : ℝ)*base75 + (1273767945183933173/247150000000000000000000000000000 : ℝ)*base77 + (907210759365216827/247150000000000000000000000000000 : ℝ)*base80 + (4876010814833/4943000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (971647/125000000000000000000 : ℝ)*base89 + (971647/125000000000000000000 : ℝ)*base91 + (971647/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1576_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1576_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1576_s4_0 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-177742803/1000000000 : ℝ)*x 0 + (1085035987/2000000000 : ℝ)*x 1 + (5220126167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177742803/1000000000 : ℝ)^4649 ≤ (2182233417153/20000000000000 : ℝ)^3625 := by
    have hnat : (177742803 : ℕ)^4649*20000000000000^3625 ≤ 2182233417153^3625*1000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177742803 1000000000 2182233417153 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085035987/2000000000 : ℝ)^4649 ≤ (45644738401697/100000000000000 : ℝ)^3625 := by
    have hnat : (1085035987 : ℕ)^4649*100000000000000^3625 ≤ 45644738401697^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085035987 2000000000 45644738401697 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220126167/10000000000 : ℝ)^4649 ≤ (43444094502927/100000000000000 : ℝ)^3625 := by
    have hnat : (5220126167 : ℕ)^4649*100000000000000^3625 ≤ 43444094502927^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220126167 10000000000 43444094502927 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-177742803/1000000000 : ℝ), (1085035987/2000000000 : ℝ), (5220126167/10000000000 : ℝ)] ![(2182233417153/20000000000000 : ℝ), (45644738401697/100000000000000 : ℝ), (43444094502927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-177742803/1000000000 : ℝ)|^4649 ≤ (2182233417153/20000000000000 : ℝ)^3625
        have hw : |(-177742803/1000000000 : ℝ)|=(177742803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085035987/2000000000 : ℝ)|^4649 ≤ (45644738401697/100000000000000 : ℝ)^3625
        have hw : |(1085035987/2000000000 : ℝ)|=(1085035987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220126167/10000000000 : ℝ)|^4649 ≤ (43444094502927/100000000000000 : ℝ)^3625
        have hw : |(5220126167/10000000000 : ℝ)|=(5220126167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_1 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347860401/10000000000 : ℝ)*x 0 + (-1882322567/10000000000 : ℝ)*x 1 + (5220126183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347860401/10000000000 : ℝ)^4649 ≤ (11203033246201/25000000000000 : ℝ)^3625 := by
    have hnat : (5347860401 : ℕ)^4649*25000000000000^3625 ≤ 11203033246201^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347860401 10000000000 11203033246201 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882322567/10000000000 : ℝ)^4649 ≤ (2348754465317/20000000000000 : ℝ)^3625 := by
    have hnat : (1882322567 : ℕ)^4649*20000000000000^3625 ≤ 2348754465317^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882322567 10000000000 2348754465317 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220126183/10000000000 : ℝ)^4649 ≤ (43444094673701/100000000000000 : ℝ)^3625 := by
    have hnat : (5220126183 : ℕ)^4649*100000000000000^3625 ≤ 43444094673701^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220126183 10000000000 43444094673701 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347860401/10000000000 : ℝ), (-1882322567/10000000000 : ℝ), (5220126183/10000000000 : ℝ)] ![(11203033246201/25000000000000 : ℝ), (2348754465317/20000000000000 : ℝ), (43444094673701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347860401/10000000000 : ℝ)|^4649 ≤ (11203033246201/25000000000000 : ℝ)^3625
        have hw : |(5347860401/10000000000 : ℝ)|=(5347860401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882322567/10000000000 : ℝ)|^4649 ≤ (2348754465317/20000000000000 : ℝ)^3625
        have hw : |(-1882322567/10000000000 : ℝ)|=(1882322567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220126183/10000000000 : ℝ)|^4649 ≤ (43444094673701/100000000000000 : ℝ)^3625
        have hw : |(5220126183/10000000000 : ℝ)|=(5220126183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_2 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673930203/5000000000 : ℝ)*x 0 + (2610063089/5000000000 : ℝ)*x 1 + (-1882322567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673930203/5000000000 : ℝ)^4649 ≤ (5601516629817/12500000000000 : ℝ)^3625 := by
    have hnat : (2673930203 : ℕ)^4649*12500000000000^3625 ≤ 5601516629817^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673930203 5000000000 5601516629817 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610063089/5000000000 : ℝ)^4649 ≤ (21722047310167/50000000000000 : ℝ)^3625 := by
    have hnat : (2610063089 : ℕ)^4649*50000000000000^3625 ≤ 21722047310167^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610063089 5000000000 21722047310167 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882322567/10000000000 : ℝ)^4649 ≤ (2348754465317/20000000000000 : ℝ)^3625 := by
    have hnat : (1882322567 : ℕ)^4649*20000000000000^3625 ≤ 2348754465317^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882322567 10000000000 2348754465317 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673930203/5000000000 : ℝ), (2610063089/5000000000 : ℝ), (-1882322567/10000000000 : ℝ)] ![(5601516629817/12500000000000 : ℝ), (21722047310167/50000000000000 : ℝ), (2348754465317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673930203/5000000000 : ℝ)|^4649 ≤ (5601516629817/12500000000000 : ℝ)^3625
        have hw : |(2673930203/5000000000 : ℝ)|=(2673930203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610063089/5000000000 : ℝ)|^4649 ≤ (21722047310167/50000000000000 : ℝ)^3625
        have hw : |(2610063089/5000000000 : ℝ)|=(2610063089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882322567/10000000000 : ℝ)|^4649 ≤ (2348754465317/20000000000000 : ℝ)^3625
        have hw : |(-1882322567/10000000000 : ℝ)|=(1882322567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_3 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120428499/5000000000 : ℝ)*x 0 + (4003458281/10000000000 : ℝ)*x 1 + (4489479423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120428499/5000000000 : ℝ)^4649 ≤ (33282481667633/100000000000000 : ℝ)^3625 := by
    have hnat : (2120428499 : ℕ)^4649*100000000000000^3625 ≤ 33282481667633^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120428499 5000000000 33282481667633 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003458281/10000000000 : ℝ)^4649 ≤ (30912215761709/100000000000000 : ℝ)^3625 := by
    have hnat : (4003458281 : ℕ)^4649*100000000000000^3625 ≤ 30912215761709^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003458281 10000000000 30912215761709 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489479423/10000000000 : ℝ)^4649 ≤ (17902651276681/50000000000000 : ℝ)^3625 := by
    have hnat : (4489479423 : ℕ)^4649*50000000000000^3625 ≤ 17902651276681^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489479423 10000000000 17902651276681 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120428499/5000000000 : ℝ), (4003458281/10000000000 : ℝ), (4489479423/10000000000 : ℝ)] ![(33282481667633/100000000000000 : ℝ), (30912215761709/100000000000000 : ℝ), (17902651276681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120428499/5000000000 : ℝ)|^4649 ≤ (33282481667633/100000000000000 : ℝ)^3625
        have hw : |(2120428499/5000000000 : ℝ)|=(2120428499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003458281/10000000000 : ℝ)|^4649 ≤ (30912215761709/100000000000000 : ℝ)^3625
        have hw : |(4003458281/10000000000 : ℝ)|=(4003458281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489479423/10000000000 : ℝ)|^4649 ≤ (17902651276681/50000000000000 : ℝ)^3625
        have hw : |(4489479423/10000000000 : ℝ)|=(4489479423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_4 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777454681/10000000000 : ℝ)*x 0 + (2610598531/5000000000 : ℝ)*x 1 + (43392809/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777454681/10000000000 : ℝ)^4649 ≤ (5455688452463/50000000000000 : ℝ)^3625 := by
    have hnat : (1777454681 : ℕ)^4649*50000000000000^3625 ≤ 5455688452463^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777454681 10000000000 5455688452463 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610598531/5000000000 : ℝ)^4649 ≤ (43455524885309/100000000000000 : ℝ)^3625 := by
    have hnat : (2610598531 : ℕ)^4649*100000000000000^3625 ≤ 43455524885309^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610598531 5000000000 43455524885309 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43392809/80000000 : ℝ)^4649 ≤ (22816549095039/50000000000000 : ℝ)^3625 := by
    have hnat : (43392809 : ℕ)^4649*50000000000000^3625 ≤ 22816549095039^3625*80000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43392809 80000000 22816549095039 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777454681/10000000000 : ℝ), (2610598531/5000000000 : ℝ), (43392809/80000000 : ℝ)] ![(5455688452463/50000000000000 : ℝ), (43455524885309/100000000000000 : ℝ), (22816549095039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777454681/10000000000 : ℝ)|^4649 ≤ (5455688452463/50000000000000 : ℝ)^3625
        have hw : |(-1777454681/10000000000 : ℝ)|=(1777454681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610598531/5000000000 : ℝ)|^4649 ≤ (43455524885309/100000000000000 : ℝ)^3625
        have hw : |(2610598531/5000000000 : ℝ)|=(2610598531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43392809/80000000 : ℝ)|^4649 ≤ (22816549095039/50000000000000 : ℝ)^3625
        have hw : |(43392809/80000000 : ℝ)|=(43392809/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_5 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646785553/5000000000 : ℝ)*x 0 + (-83917389/500000000 : ℝ)*x 1 + (542410107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646785553/5000000000 : ℝ)^4649 ≤ (44229551575839/100000000000000 : ℝ)^3625 := by
    have hnat : (2646785553 : ℕ)^4649*100000000000000^3625 ≤ 44229551575839^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646785553 5000000000 44229551575839 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83917389/500000000 : ℝ)^4649 ≤ (5068675405033/50000000000000 : ℝ)^3625 := by
    have hnat : (83917389 : ℕ)^4649*50000000000000^3625 ≤ 5068675405033^3625*500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83917389 500000000 5068675405033 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542410107/1000000000 : ℝ)^4649 ≤ (11408274399163/25000000000000 : ℝ)^3625 := by
    have hnat : (542410107 : ℕ)^4649*25000000000000^3625 ≤ 11408274399163^3625*1000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542410107 1000000000 11408274399163 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646785553/5000000000 : ℝ), (-83917389/500000000 : ℝ), (542410107/1000000000 : ℝ)] ![(44229551575839/100000000000000 : ℝ), (5068675405033/50000000000000 : ℝ), (11408274399163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646785553/5000000000 : ℝ)|^4649 ≤ (44229551575839/100000000000000 : ℝ)^3625
        have hw : |(2646785553/5000000000 : ℝ)|=(2646785553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83917389/500000000 : ℝ)|^4649 ≤ (5068675405033/50000000000000 : ℝ)^3625
        have hw : |(-83917389/500000000 : ℝ)|=(83917389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542410107/1000000000 : ℝ)|^4649 ≤ (11408274399163/25000000000000 : ℝ)^3625
        have hw : |(542410107/1000000000 : ℝ)|=(542410107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_6 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293571253/10000000000 : ℝ)*x 0 + (2712050517/5000000000 : ℝ)*x 1 + (-1678347627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293571253/10000000000 : ℝ)^4649 ≤ (11057388287757/25000000000000 : ℝ)^3625 := by
    have hnat : (5293571253 : ℕ)^4649*25000000000000^3625 ≤ 11057388287757^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293571253 10000000000 11057388287757 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712050517/5000000000 : ℝ)^4649 ≤ (11408274302057/25000000000000 : ℝ)^3625 := by
    have hnat : (2712050517 : ℕ)^4649*25000000000000^3625 ≤ 11408274302057^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712050517 5000000000 11408274302057 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678347627/10000000000 : ℝ)^4649 ≤ (10137349624883/100000000000000 : ℝ)^3625 := by
    have hnat : (1678347627 : ℕ)^4649*100000000000000^3625 ≤ 10137349624883^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678347627 10000000000 10137349624883 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293571253/10000000000 : ℝ), (2712050517/5000000000 : ℝ), (-1678347627/10000000000 : ℝ)] ![(11057388287757/25000000000000 : ℝ), (11408274302057/25000000000000 : ℝ), (10137349624883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293571253/10000000000 : ℝ)|^4649 ≤ (11057388287757/25000000000000 : ℝ)^3625
        have hw : |(5293571253/10000000000 : ℝ)|=(5293571253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712050517/5000000000 : ℝ)|^4649 ≤ (11408274302057/25000000000000 : ℝ)^3625
        have hw : |(2712050517/5000000000 : ℝ)|=(2712050517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1678347627/10000000000 : ℝ)|^4649 ≤ (10137349624883/100000000000000 : ℝ)^3625
        have hw : |(-1678347627/10000000000 : ℝ)|=(1678347627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s4_7 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848184041/2000000000 : ℝ)*x 0 + (448694133/1000000000 : ℝ)*x 1 + (2003007591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848184041/2000000000 : ℝ)^4649 ≤ (33283117847177/100000000000000 : ℝ)^3625 := by
    have hnat : (848184041 : ℕ)^4649*100000000000000^3625 ≤ 33283117847177^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848184041 2000000000 33283117847177 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448694133/1000000000 : ℝ)^4649 ≤ (178896721417/500000000000 : ℝ)^3625 := by
    have hnat : (448694133 : ℕ)^4649*500000000000^3625 ≤ 178896721417^3625*1000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448694133 1000000000 178896721417 500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003007591/5000000000 : ℝ)^4649 ≤ (30937537845749/100000000000000 : ℝ)^3625 := by
    have hnat : (2003007591 : ℕ)^4649*100000000000000^3625 ≤ 30937537845749^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003007591 5000000000 30937537845749 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848184041/2000000000 : ℝ), (448694133/1000000000 : ℝ), (2003007591/5000000000 : ℝ)] ![(33283117847177/100000000000000 : ℝ), (178896721417/500000000000 : ℝ), (30937537845749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848184041/2000000000 : ℝ)|^4649 ≤ (33283117847177/100000000000000 : ℝ)^3625
        have hw : |(848184041/2000000000 : ℝ)|=(848184041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448694133/1000000000 : ℝ)|^4649 ≤ (178896721417/500000000000 : ℝ)^3625
        have hw : |(448694133/1000000000 : ℝ)|=(448694133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003007591/5000000000 : ℝ)|^4649 ≤ (30937537845749/100000000000000 : ℝ)^3625
        have hw : |(2003007591/5000000000 : ℝ)|=(2003007591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1576_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1111/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1111/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1111/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1111/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1111/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1111/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1111/10000 : ℝ) ^ (4647/1024 : ℝ) ≤ (1167638480792883/25000000000000000000 : ℝ) := by
    have hpowers : (1111/10000 : ℝ)^4647 ≤ (1167638480792883/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1111 : ℕ)^4647*25000000000000000000^1024 ≤ 1167638480792883^1024*10000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1111 10000 1167638480792883 25000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1111/10000 : ℝ)) (X := (1167638480792883/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15517/100000 : ℝ) ^ (4647/1024 : ℝ) ≤ (10636189830794247/50000000000000000000 : ℝ) := by
    have hpowers : (15517/100000 : ℝ)^4647 ≤ (10636189830794247/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15517 : ℕ)^4647*50000000000000000000^1024 ≤ 10636189830794247^1024*100000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15517 100000 10636189830794247 50000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15517/100000 : ℝ)) (X := (10636189830794247/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501167638480792883/12500000000000000000 : ℝ) ≤ (2500051457640127/2500000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (12501167638480792883/12500000000000000000 : ℝ)^1024 ≤ (2500051457640127/2500000000000000 : ℝ)^4647 := by
      have hnat : (12501167638480792883 : ℕ)^1024*2500000000000000^4647 ≤ 2500051457640127^4647*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501167638480792883 12500000000000000000 2500051457640127 2500000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500051457640127/2500000000000000 : ℝ)) (X := (12501167638480792883/12500000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012971466792380013/50000000000000000000 : ℝ) ≤ (10000571613466739/10000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (50012971466792380013/50000000000000000000 : ℝ)^1024 ≤ (10000571613466739/10000000000000000 : ℝ)^4647 := by
      have hnat : (50012971466792380013 : ℕ)^1024*10000000000000000^4647 ≤ 10000571613466739^4647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012971466792380013 50000000000000000000 10000571613466739 10000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000571613466739/10000000000000000 : ℝ)) (X := (50012971466792380013/50000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010636189830794247/25000000000000000000 : ℝ) ≤ (1000093739637297/1000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (25010636189830794247/25000000000000000000 : ℝ)^1024 ≤ (1000093739637297/1000000000000000 : ℝ)^4647 := by
      have hnat : (25010636189830794247 : ℕ)^1024*1000000000000000^4647 ≤ 1000093739637297^4647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010636189830794247 25000000000000000000 1000093739637297 1000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000093739637297/1000000000000000 : ℝ)) (X := (25010636189830794247/25000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1167638480792883/25000000000000000000 : ℝ) ≤ ((2753923712443981621/2754375000000000000 : ℝ)+2*(365782906231/440700000000000 : ℝ)*(1111/10000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (2753923712443981621/2754375000000000000 : ℝ)+2*(365782906231/440700000000000 : ℝ)*(1111/10000 : ℝ)=(2500051457640127/2500000000000000 : ℝ) by norm_num, show 1+2*(1167638480792883/25000000000000000000 : ℝ)=(12501167638480792883/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10636189830794247/50000000000000000000 : ℝ)+(1167638480792883/25000000000000000000 : ℝ) ≤ ((2753923712443981621/2754375000000000000 : ℝ)+(365782906231/440700000000000 : ℝ)*((15517/100000 : ℝ)+(1111/10000 : ℝ)))^(4647/1024 : ℝ) := by
    rw [show (2753923712443981621/2754375000000000000 : ℝ)+(365782906231/440700000000000 : ℝ)*((15517/100000 : ℝ)+(1111/10000 : ℝ))=(10000571613466739/10000000000000000 : ℝ) by norm_num, show 1+(10636189830794247/50000000000000000000 : ℝ)+(1167638480792883/25000000000000000000 : ℝ)=(50012971466792380013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10636189830794247/50000000000000000000 : ℝ) ≤ ((2753923712443981621/2754375000000000000 : ℝ)+2*(365782906231/440700000000000 : ℝ)*(15517/100000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (2753923712443981621/2754375000000000000 : ℝ)+2*(365782906231/440700000000000 : ℝ)*(15517/100000 : ℝ)=(1000093739637297/1000000000000000 : ℝ) by norm_num, show 1+2*(10636189830794247/50000000000000000000 : ℝ)=(25010636189830794247/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2753923712443981621/2754375000000000000 : ℝ)*(X 1 0+X 2 0)+(365782906231/440700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (1111/10000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (2753923712443981621/2754375000000000000 : ℝ)) (alpha := (365782906231/440700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2753923712443981621/2754375000000000000 : ℝ)*(X 0 1+X 2 1)+(365782906231/440700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (1111/10000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (2753923712443981621/2754375000000000000 : ℝ)) (alpha := (365782906231/440700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2753923712443981621/2754375000000000000 : ℝ)*(X 0 2+X 1 2)+(365782906231/440700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (1111/10000 : ℝ)) (hi := (15517/100000 : ℝ)) (c := (2753923712443981621/2754375000000000000 : ℝ)) (alpha := (365782906231/440700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-177742803/1000000000 : ℝ)*X 0 0+(1085035987/2000000000 : ℝ)*X 0 1+(5220126167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347860401/10000000000 : ℝ)*X 1 0+(-1882322567/10000000000 : ℝ)*X 1 1+(5220126183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673930203/5000000000 : ℝ)*X 2 0+(2610063089/5000000000 : ℝ)*X 2 1+(-1882322567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2120428499/5000000000 : ℝ)*X 0 0+(4003458281/10000000000 : ℝ)*X 0 1+(4489479423/10000000000 : ℝ)*X 0 2+(2120428499/5000000000 : ℝ)*X 1 0+(4003458281/10000000000 : ℝ)*X 1 1+(4489479423/10000000000 : ℝ)*X 1 2+(2120428499/5000000000 : ℝ)*X 2 0+(4003458281/10000000000 : ℝ)*X 2 1+(4489479423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1777454681/10000000000 : ℝ)*X 0 0+(2610598531/5000000000 : ℝ)*X 0 1+(43392809/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646785553/5000000000 : ℝ)*X 1 0+(-83917389/500000000 : ℝ)*X 1 1+(542410107/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293571253/10000000000 : ℝ)*X 2 0+(2712050517/5000000000 : ℝ)*X 2 1+(-1678347627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848184041/2000000000 : ℝ)*X 0 0+(448694133/1000000000 : ℝ)*X 0 1+(2003007591/5000000000 : ℝ)*X 0 2+(848184041/2000000000 : ℝ)*X 1 0+(448694133/1000000000 : ℝ)*X 1 1+(2003007591/5000000000 : ℝ)*X 1 2+(848184041/2000000000 : ℝ)*X 2 0+(448694133/1000000000 : ℝ)*X 2 1+(2003007591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94770500274910629699824123/22953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (690799111/100000000000000 : ℝ)*(base19) + (326804639/50000000000000 : ℝ)*(base23) + (22326999/100000000000000 : ℝ)*(lower2) + (103041927/100000000000000 : ℝ)*(upper3) + (18441121/25000000000000 : ℝ)*(upper5) + (3467163193914187/100000000000000 : ℝ)*(major0) + (3467163193914187/100000000000000 : ℝ)*(major1) + (3467163193914187/100000000000000 : ℝ)*(major2) + (2438390763524953/50000000000000 : ℝ)*(sp0) + (2438396177513767/50000000000000 : ℝ)*(sp1) + (4876792392217367/100000000000000 : ℝ)*(sp2) + (1028764088883211/50000000000000 : ℝ)*(sp3) + (11518776739/100000000000000 : ℝ)*(sp4) + (2513303127/50000000000000 : ℝ)*(sp7) + (514383301093169/25000000000000 : ℝ)*(f.failure) + (975358609165329/20000000000000 : ℝ)*(f.sum) + (8579586765587/5508750000000000000000000000 : ℝ)*base66 + (33412510867263377/275437500000000000000000000000000 : ℝ)*base67 + (424944415869325877/275437500000000000000000000000000 : ℝ)*base69 + (509377041166638377/275437500000000000000000000000000 : ℝ)*base71 + (50718996319357/22035000000000000000000000000 : ℝ)*base73 + (243127834287138377/275437500000000000000000000000000 : ℝ)*base75 + (1468702118100611623/275437500000000000000000000000000 : ℝ)*base78 + (4532035032993138377/275437500000000000000000000000000 : ℝ)*base79 + (22473981625811/11017500000000000000000000000 : ℝ)*base81 + (586377/62500000000000000000 : ℝ)*base90 + (586377/62500000000000000000 : ℝ)*base92 + (586377/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1937148185506275808728513/406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (604196687/100000000000000 : ℝ)*(base19) + (433515923/50000000000000 : ℝ)*(base23) + (2775691/2500000000000 : ℝ)*(upper3) + (3408493/10000000000000 : ℝ)*(lower4) + (15880983/20000000000000 : ℝ)*(upper5) + (3503879524622487/100000000000000 : ℝ)*(major0) + (3503879524622487/100000000000000 : ℝ)*(major1) + (3503879524622487/100000000000000 : ℝ)*(major2) + (3391109987/50000000000000 : ℝ)*(sp1) + (1598406633/12500000000000 : ℝ)*(sp2) + (61605461996397/1250000000000 : ℝ)*(sp4) + (4928429573295099/100000000000000 : ℝ)*(sp5) + (98568466108537/2000000000000 : ℝ)*(sp6) + (415864386117543/20000000000000 : ℝ)*(sp7) + (415864386117543/20000000000000 : ℝ)*(f.failure) + (61605461996397/1250000000000 : ℝ)*(f.sum) + (508193747419/1836250000000000000000000000 : ℝ)*base66 + (349766467629597559/91812500000000000000000000000000 : ℝ)*base67 + (361306467058347559/91812500000000000000000000000000 : ℝ)*base69 + (454677804396035059/91812500000000000000000000000000 : ℝ)*base71 + (403234973659/7345000000000000000000000000 : ℝ)*base73 + (1466462235954097559/91812500000000000000000000000000 : ℝ)*base75 + (508069714267660059/91812500000000000000000000000000 : ℝ)*base77 + (779942627650347559/91812500000000000000000000000000 : ℝ)*base79 + (19664270306241/7345000000000000000000000000 : ℝ)*base82 + (228519/50000000000000000000 : ℝ)*base90 + (228519/50000000000000000000 : ℝ)*base92 + (228519/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1576_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1576_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1576_s5_0 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111090557/625000000 : ℝ)*x 0 + (2712518469/5000000000 : ℝ)*x 1 + (208810213/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111090557/625000000 : ℝ)^4649 ≤ (5455665743207/50000000000000 : ℝ)^3625 := by
    have hnat : (111090557 : ℕ)^4649*50000000000000^3625 ≤ 5455665743207^3625*625000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111090557 625000000 5455665743207 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712518469/5000000000 : ℝ)^4649 ≤ (2852699715383/6250000000000 : ℝ)^3625 := by
    have hnat : (2712518469 : ℕ)^4649*6250000000000^3625 ≤ 2852699715383^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712518469 5000000000 2852699715383 6250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208810213/400000000 : ℝ)^4649 ≤ (2172273652899/5000000000000 : ℝ)^3625 := by
    have hnat : (208810213 : ℕ)^4649*5000000000000^3625 ≤ 2172273652899^3625*400000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208810213 400000000 2172273652899 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111090557/625000000 : ℝ), (2712518469/5000000000 : ℝ), (208810213/400000000 : ℝ)] ![(5455665743207/50000000000000 : ℝ), (2852699715383/6250000000000 : ℝ), (2172273652899/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111090557/625000000 : ℝ)|^4649 ≤ (5455665743207/50000000000000 : ℝ)^3625
        have hw : |(-111090557/625000000 : ℝ)|=(111090557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712518469/5000000000 : ℝ)|^4649 ≤ (2852699715383/6250000000000 : ℝ)^3625
        have hw : |(2712518469/5000000000 : ℝ)|=(2712518469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208810213/400000000 : ℝ)|^4649 ≤ (2172273652899/5000000000000 : ℝ)^3625
        have hw : |(208810213/400000000 : ℝ)|=(208810213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_1 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673911283/5000000000 : ℝ)*x 0 + (-941100557/5000000000 : ℝ)*x 1 + (208810213/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673911283/5000000000 : ℝ)^4649 ≤ (44811726391339/100000000000000 : ℝ)^3625 := by
    have hnat : (2673911283 : ℕ)^4649*100000000000000^3625 ≤ 44811726391339^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673911283 5000000000 44811726391339 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941100557/5000000000 : ℝ)^4649 ≤ (18348125849/156250000000 : ℝ)^3625 := by
    have hnat : (941100557 : ℕ)^4649*156250000000^3625 ≤ 18348125849^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941100557 5000000000 18348125849 156250000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208810213/400000000 : ℝ)^4649 ≤ (2172273652899/5000000000000 : ℝ)^3625 := by
    have hnat : (208810213 : ℕ)^4649*5000000000000^3625 ≤ 2172273652899^3625*400000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208810213 400000000 2172273652899 5000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673911283/5000000000 : ℝ), (-941100557/5000000000 : ℝ), (208810213/400000000 : ℝ)] ![(44811726391339/100000000000000 : ℝ), (18348125849/156250000000 : ℝ), (2172273652899/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673911283/5000000000 : ℝ)|^4649 ≤ (44811726391339/100000000000000 : ℝ)^3625
        have hw : |(2673911283/5000000000 : ℝ)|=(2673911283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941100557/5000000000 : ℝ)|^4649 ≤ (18348125849/156250000000 : ℝ)^3625
        have hw : |(-941100557/5000000000 : ℝ)|=(941100557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208810213/400000000 : ℝ)|^4649 ≤ (2172273652899/5000000000000 : ℝ)^3625
        have hw : |(208810213/400000000 : ℝ)|=(208810213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_2 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347822567/10000000000 : ℝ)*x 0 + (163132979/312500000 : ℝ)*x 1 + (-470550277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347822567/10000000000 : ℝ)^4649 ≤ (22405863201043/50000000000000 : ℝ)^3625 := by
    have hnat : (5347822567 : ℕ)^4649*50000000000000^3625 ≤ 22405863201043^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347822567 10000000000 22405863201043 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163132979/312500000 : ℝ)^4649 ≤ (4344547309/10000000000 : ℝ)^3625 := by
    have hnat : (163132979 : ℕ)^4649*10000000000^3625 ≤ 4344547309^3625*312500000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163132979 312500000 4344547309 10000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470550277/2500000000 : ℝ)^4649 ≤ (1467850061919/12500000000000 : ℝ)^3625 := by
    have hnat : (470550277 : ℕ)^4649*12500000000000^3625 ≤ 1467850061919^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470550277 2500000000 1467850061919 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347822567/10000000000 : ℝ), (163132979/312500000 : ℝ), (-470550277/2500000000 : ℝ)] ![(22405863201043/50000000000000 : ℝ), (4344547309/10000000000 : ℝ), (1467850061919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347822567/10000000000 : ℝ)|^4649 ≤ (22405863201043/50000000000000 : ℝ)^3625
        have hw : |(5347822567/10000000000 : ℝ)|=(5347822567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163132979/312500000 : ℝ)|^4649 ≤ (4344547309/10000000000 : ℝ)^3625
        have hw : |(163132979/312500000 : ℝ)|=(163132979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470550277/2500000000 : ℝ)|^4649 ≤ (1467850061919/12500000000000 : ℝ)^3625
        have hw : |(-470550277/2500000000 : ℝ)|=(470550277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_3 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120435183/5000000000 : ℝ)*x 0 + (800755861/2000000000 : ℝ)*x 1 + (2244577731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120435183/5000000000 : ℝ)^4649 ≤ (416032702707/1250000000000 : ℝ)^3625 := by
    have hnat : (2120435183 : ℕ)^4649*1250000000000^3625 ≤ 416032702707^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120435183 5000000000 416032702707 1250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800755861/2000000000 : ℝ)^4649 ≤ (30915394748947/100000000000000 : ℝ)^3625 := by
    have hnat : (800755861 : ℕ)^4649*100000000000000^3625 ≤ 30915394748947^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800755861 2000000000 30915394748947 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244577731/5000000000 : ℝ)^4649 ≤ (3580198902111/10000000000000 : ℝ)^3625 := by
    have hnat : (2244577731 : ℕ)^4649*10000000000000^3625 ≤ 3580198902111^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244577731 5000000000 3580198902111 10000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120435183/5000000000 : ℝ), (800755861/2000000000 : ℝ), (2244577731/5000000000 : ℝ)] ![(416032702707/1250000000000 : ℝ), (30915394748947/100000000000000 : ℝ), (3580198902111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120435183/5000000000 : ℝ)|^4649 ≤ (416032702707/1250000000000 : ℝ)^3625
        have hw : |(2120435183/5000000000 : ℝ)|=(2120435183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800755861/2000000000 : ℝ)|^4649 ≤ (30915394748947/100000000000000 : ℝ)^3625
        have hw : |(800755861/2000000000 : ℝ)|=(800755861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244577731/5000000000 : ℝ)|^4649 ≤ (3580198902111/10000000000000 : ℝ)^3625
        have hw : |(2244577731/5000000000 : ℝ)|=(2244577731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_4 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777475479/10000000000 : ℝ)*x 0 + (326332711/625000000 : ℝ)*x 1 + (1355990247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777475479/10000000000 : ℝ)^4649 ≤ (10911540644949/100000000000000 : ℝ)^3625 := by
    have hnat : (1777475479 : ℕ)^4649*100000000000000^3625 ≤ 10911540644949^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777475479 10000000000 10911540644949 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326332711/625000000 : ℝ)^4649 ≤ (43456873163229/100000000000000 : ℝ)^3625 := by
    have hnat : (326332711 : ℕ)^4649*100000000000000^3625 ≤ 43456873163229^3625*625000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326332711 625000000 43456873163229 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355990247/2500000000 : ℝ)^4649 ≤ (456315861791/1000000000000 : ℝ)^3625 := by
    have hnat : (1355990247 : ℕ)^4649*1000000000000^3625 ≤ 456315861791^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355990247 2500000000 456315861791 1000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777475479/10000000000 : ℝ), (326332711/625000000 : ℝ), (1355990247/2500000000 : ℝ)] ![(10911540644949/100000000000000 : ℝ), (43456873163229/100000000000000 : ℝ), (456315861791/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777475479/10000000000 : ℝ)|^4649 ≤ (10911540644949/100000000000000 : ℝ)^3625
        have hw : |(-1777475479/10000000000 : ℝ)|=(1777475479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326332711/625000000 : ℝ)|^4649 ≤ (43456873163229/100000000000000 : ℝ)^3625
        have hw : |(326332711/625000000 : ℝ)|=(326332711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355990247/2500000000 : ℝ)|^4649 ≤ (456315861791/1000000000000 : ℝ)^3625
        have hw : |(1355990247/2500000000 : ℝ)|=(1355990247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_5 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165425167/312500000 : ℝ)*x 0 + (-335699113/2000000000 : ℝ)*x 1 + (1355990241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165425167/312500000 : ℝ)^4649 ≤ (5528739806987/12500000000000 : ℝ)^3625 := by
    have hnat : (165425167 : ℕ)^4649*12500000000000^3625 ≤ 5528739806987^3625*312500000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165425167 312500000 5528739806987 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335699113/2000000000 : ℝ)^4649 ≤ (2534623902641/25000000000000 : ℝ)^3625 := by
    have hnat : (335699113 : ℕ)^4649*25000000000000^3625 ≤ 2534623902641^3625*2000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335699113 2000000000 2534623902641 25000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355990241/2500000000 : ℝ)^4649 ≤ (5703948240019/12500000000000 : ℝ)^3625 := by
    have hnat : (1355990241 : ℕ)^4649*12500000000000^3625 ≤ 5703948240019^3625*2500000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355990241 2500000000 5703948240019 12500000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165425167/312500000 : ℝ), (-335699113/2000000000 : ℝ), (1355990241/2500000000 : ℝ)] ![(5528739806987/12500000000000 : ℝ), (2534623902641/25000000000000 : ℝ), (5703948240019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165425167/312500000 : ℝ)|^4649 ≤ (5528739806987/12500000000000 : ℝ)^3625
        have hw : |(165425167/312500000 : ℝ)|=(165425167/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335699113/2000000000 : ℝ)|^4649 ≤ (2534623902641/25000000000000 : ℝ)^3625
        have hw : |(-335699113/2000000000 : ℝ)|=(335699113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355990241/2500000000 : ℝ)|^4649 ≤ (5703948240019/12500000000000 : ℝ)^3625
        have hw : |(1355990241/2500000000 : ℝ)|=(1355990241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_6 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293605427/10000000000 : ℝ)*x 0 + (135599023/250000000 : ℝ)*x 1 + (-1678495513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293605427/10000000000 : ℝ)^4649 ≤ (4422991934529/10000000000000 : ℝ)^3625 := by
    have hnat : (5293605427 : ℕ)^4649*10000000000000^3625 ≤ 4422991934529^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293605427 10000000000 4422991934529 10000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135599023/250000000 : ℝ)^4649 ≤ (9126317089083/20000000000000 : ℝ)^3625 := by
    have hnat : (135599023 : ℕ)^4649*20000000000000^3625 ≤ 9126317089083^3625*250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135599023 250000000 9126317089083 20000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678495513/10000000000 : ℝ)^4649 ≤ (5069247603873/50000000000000 : ℝ)^3625 := by
    have hnat : (1678495513 : ℕ)^4649*50000000000000^3625 ≤ 5069247603873^3625*10000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678495513 10000000000 5069247603873 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293605427/10000000000 : ℝ), (135599023/250000000 : ℝ), (-1678495513/10000000000 : ℝ)] ![(4422991934529/10000000000000 : ℝ), (9126317089083/20000000000000 : ℝ), (5069247603873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293605427/10000000000 : ℝ)|^4649 ≤ (4422991934529/10000000000000 : ℝ)^3625
        have hw : |(5293605427/10000000000 : ℝ)|=(5293605427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135599023/250000000 : ℝ)|^4649 ≤ (9126317089083/20000000000000 : ℝ)^3625
        have hw : |(135599023/250000000 : ℝ)|=(135599023/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1678495513/10000000000 : ℝ)|^4649 ≤ (5069247603873/50000000000000 : ℝ)^3625
        have hw : |(-1678495513/10000000000 : ℝ)|=(1678495513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1576_s5_7 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530116679/1250000000 : ℝ)*x 0 + (2243311999/5000000000 : ℝ)*x 1 + (2003164697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530116679/1250000000 : ℝ)^4649 ≤ (33283250977499/100000000000000 : ℝ)^3625 := by
    have hnat : (530116679 : ℕ)^4649*100000000000000^3625 ≤ 33283250977499^3625*1250000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530116679 1250000000 33283250977499 100000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243311999/5000000000 : ℝ)^4649 ≤ (17888049535779/50000000000000 : ℝ)^3625 := by
    have hnat : (2243311999 : ℕ)^4649*50000000000000^3625 ≤ 17888049535779^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243311999 5000000000 17888049535779 50000000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003164697/5000000000 : ℝ)^4649 ≤ (1933790621039/6250000000000 : ℝ)^3625 := by
    have hnat : (2003164697 : ℕ)^4649*6250000000000^3625 ≤ 1933790621039^3625*5000000000^4649 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003164697 5000000000 1933790621039 6250000000000 4649 3625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4649/1024 : ℝ)) 4649 3625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530116679/1250000000 : ℝ), (2243311999/5000000000 : ℝ), (2003164697/5000000000 : ℝ)] ![(33283250977499/100000000000000 : ℝ), (17888049535779/50000000000000 : ℝ), (1933790621039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530116679/1250000000 : ℝ)|^4649 ≤ (33283250977499/100000000000000 : ℝ)^3625
        have hw : |(530116679/1250000000 : ℝ)|=(530116679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243311999/5000000000 : ℝ)|^4649 ≤ (17888049535779/50000000000000 : ℝ)^3625
        have hw : |(2243311999/5000000000 : ℝ)|=(2243311999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003164697/5000000000 : ℝ)|^4649 ≤ (1933790621039/6250000000000 : ℝ)^3625
        have hw : |(2003164697/5000000000 : ℝ)|=(2003164697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1576_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (557/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5569/50000 : ℝ) ^ (4647/1024 : ℝ) ≤ (295263142354663/6250000000000000000 : ℝ) := by
    have hpowers : (5569/50000 : ℝ)^4647 ≤ (295263142354663/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5569 : ℕ)^4647*6250000000000000000^1024 ≤ 295263142354663^1024*50000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5569 50000 295263142354663 6250000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5569/50000 : ℝ)) (X := (295263142354663/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15487/100000 : ℝ) ^ (4647/1024 : ℝ) ≤ (10543189004929303/50000000000000000000 : ℝ) := by
    have hpowers : (15487/100000 : ℝ)^4647 ≤ (10543189004929303/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15487 : ℕ)^4647*50000000000000000000^1024 ≤ 10543189004929303^1024*100000^4647 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15487 100000 10543189004929303 50000000000000000000 4647 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15487/100000 : ℝ)) (X := (10543189004929303/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125295263142354663/3125000000000000000 : ℝ) ≤ (5000104097550169/5000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (3125295263142354663/3125000000000000000 : ℝ)^1024 ≤ (5000104097550169/5000000000000000 : ℝ)^4647 := by
      have hnat : (3125295263142354663 : ℕ)^1024*5000000000000000^4647 ≤ 5000104097550169^4647*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125295263142354663 3125000000000000000 5000104097550169 5000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000104097550169/5000000000000000 : ℝ)) (X := (3125295263142354663/3125000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012905294143766607/50000000000000000000 : ℝ) ≤ (2500142174432697/2500000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (50012905294143766607/50000000000000000000 : ℝ)^1024 ≤ (2500142174432697/2500000000000000 : ℝ)^4647 := by
      have hnat : (50012905294143766607 : ℕ)^1024*2500000000000000^4647 ≤ 2500142174432697^4647*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012905294143766607 50000000000000000000 2500142174432697 2500000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500142174432697/2500000000000000 : ℝ)) (X := (50012905294143766607/50000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010543189004929303/25000000000000000000 : ℝ) ≤ (5000464600180619/5000000000000000 : ℝ) ^ (4647/1024 : ℝ) := by
    have hpowers : (25010543189004929303/25000000000000000000 : ℝ)^1024 ≤ (5000464600180619/5000000000000000 : ℝ)^4647 := by
      have hnat : (25010543189004929303 : ℕ)^1024*5000000000000000^4647 ≤ 5000464600180619^4647*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010543189004929303 25000000000000000000 5000464600180619 5000000000000000 1024 4647 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000464600180619/5000000000000000 : ℝ)) (X := (25010543189004929303/25000000000000000000 : ℝ)) (by norm_num) 4647 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(295263142354663/6250000000000000000 : ℝ) ≤ ((21741437441947732881/21745000000000000000 : ℝ)+2*(7210052609/8698000000000 : ℝ)*(5569/50000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (21741437441947732881/21745000000000000000 : ℝ)+2*(7210052609/8698000000000 : ℝ)*(5569/50000 : ℝ)=(5000104097550169/5000000000000000 : ℝ) by norm_num, show 1+2*(295263142354663/6250000000000000000 : ℝ)=(3125295263142354663/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10543189004929303/50000000000000000000 : ℝ)+(295263142354663/6250000000000000000 : ℝ) ≤ ((21741437441947732881/21745000000000000000 : ℝ)+(7210052609/8698000000000 : ℝ)*((15487/100000 : ℝ)+(5569/50000 : ℝ)))^(4647/1024 : ℝ) := by
    rw [show (21741437441947732881/21745000000000000000 : ℝ)+(7210052609/8698000000000 : ℝ)*((15487/100000 : ℝ)+(5569/50000 : ℝ))=(2500142174432697/2500000000000000 : ℝ) by norm_num, show 1+(10543189004929303/50000000000000000000 : ℝ)+(295263142354663/6250000000000000000 : ℝ)=(50012905294143766607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10543189004929303/50000000000000000000 : ℝ) ≤ ((21741437441947732881/21745000000000000000 : ℝ)+2*(7210052609/8698000000000 : ℝ)*(15487/100000 : ℝ))^(4647/1024 : ℝ) := by
    rw [show (21741437441947732881/21745000000000000000 : ℝ)+2*(7210052609/8698000000000 : ℝ)*(15487/100000 : ℝ)=(5000464600180619/5000000000000000 : ℝ) by norm_num, show 1+2*(10543189004929303/50000000000000000000 : ℝ)=(25010543189004929303/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21741437441947732881/21745000000000000000 : ℝ)*(X 1 0+X 2 0)+(7210052609/8698000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (21741437441947732881/21745000000000000000 : ℝ)) (alpha := (7210052609/8698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21741437441947732881/21745000000000000000 : ℝ)*(X 0 1+X 2 1)+(7210052609/8698000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (21741437441947732881/21745000000000000000 : ℝ)) (alpha := (7210052609/8698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21741437441947732881/21745000000000000000 : ℝ)*(X 0 2+X 1 2)+(7210052609/8698000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4647/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (21741437441947732881/21745000000000000000 : ℝ)) (alpha := (7210052609/8698000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-111090557/625000000 : ℝ)*X 0 0+(2712518469/5000000000 : ℝ)*X 0 1+(208810213/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673911283/5000000000 : ℝ)*X 1 0+(-941100557/5000000000 : ℝ)*X 1 1+(208810213/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347822567/10000000000 : ℝ)*X 2 0+(163132979/312500000 : ℝ)*X 2 1+(-470550277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2120435183/5000000000 : ℝ)*X 0 0+(800755861/2000000000 : ℝ)*X 0 1+(2244577731/5000000000 : ℝ)*X 0 2+(2120435183/5000000000 : ℝ)*X 1 0+(800755861/2000000000 : ℝ)*X 1 1+(2244577731/5000000000 : ℝ)*X 1 2+(2120435183/5000000000 : ℝ)*X 2 0+(800755861/2000000000 : ℝ)*X 2 1+(2244577731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1777475479/10000000000 : ℝ)*X 0 0+(326332711/625000000 : ℝ)*X 0 1+(1355990247/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165425167/312500000 : ℝ)*X 1 0+(-335699113/2000000000 : ℝ)*X 1 1+(1355990241/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293605427/10000000000 : ℝ)*X 2 0+(135599023/250000000 : ℝ)*X 2 1+(-1678495513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530116679/1250000000 : ℝ)*X 0 0+(2243311999/5000000000 : ℝ)*X 0 1+(2003164697/5000000000 : ℝ)*X 0 2+(530116679/1250000000 : ℝ)*X 1 0+(2243311999/5000000000 : ℝ)*X 1 1+(2003164697/5000000000 : ℝ)*X 1 2+(530116679/1250000000 : ℝ)*X 2 0+(2243311999/5000000000 : ℝ)*X 2 1+(2003164697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1576_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53189157929570756195763/4349000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2046952571/100000000000000 : ℝ)*(base19) + (239312063/12500000000000 : ℝ)*(base23) + (35661743/50000000000000 : ℝ)*(lower2) + (295199953/100000000000000 : ℝ)*(upper3) + (205388303/100000000000000 : ℝ)*(upper5) + (3471803029904939/100000000000000 : ℝ)*(major0) + (3471803029904939/100000000000000 : ℝ)*(major1) + (3471803029904939/100000000000000 : ℝ)*(major2) + (4883285472270077/100000000000000 : ℝ)*(sp0) + (4883316963467741/100000000000000 : ℝ)*(sp1) + (152603659247619/3125000000000 : ℝ)*(sp2) + (412054285777857/20000000000000 : ℝ)*(sp3) + (8384537559/25000000000000 : ℝ)*(sp4) + (38032067/250000000000 : ℝ)*(sp7) + (412057328343217/20000000000000 : ℝ)*(f.failure) + (610414876302539/12500000000000 : ℝ)*(f.sum) + (1773474974387/1087250000000000000000000000 : ℝ)*base66 + (22128780641459400741/2174500000000000000000000000000000 : ℝ)*base68 + (25464404442871400741/2174500000000000000000000000000000 : ℝ)*base70 + (13416607437980099259/2174500000000000000000000000000000 : ℝ)*base71 + (11218461963489/4349000000000000000000000000 : ℝ)*base74 + (4159749241344599259/2174500000000000000000000000000000 : ℝ)*base75 + (10802571991095099259/2174500000000000000000000000000000 : ℝ)*base77 + (18497861562278400741/2174500000000000000000000000000000 : ℝ)*base80 + (2498948734123/543625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (248561/50000000000000000000 : ℝ)*base90 + (248561/50000000000000000000 : ℝ)*base92 + (248561/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5083066745119198786562208279/1087250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614229327/100000000000000 : ℝ)*(base19) + (51122571/6250000000000 : ℝ)*(base23) + (1857337/1250000000000 : ℝ)*(lower1) + (12064299/10000000000000 : ℝ)*(upper3) + (23320881/50000000000000 : ℝ)*(lower4) + (2810179/3125000000000 : ℝ)*(upper5) + (3508481100061453/100000000000000 : ℝ)*(major0) + (3508481100061453/100000000000000 : ℝ)*(major1) + (3508481100061453/100000000000000 : ℝ)*(major2) + (3734257267/100000000000000 : ℝ)*(sp2) + (2467454690736471/50000000000000 : ℝ)*(sp4) + (986981753448723/20000000000000 : ℝ)*(sp5) + (246745241462727/5000000000000 : ℝ)*(sp6) + (1041026331405657/50000000000000 : ℝ)*(sp7) + (1041026331405657/50000000000000 : ℝ)*(f.failure) + (2467454690736471/50000000000000 : ℝ)*(f.sum) + (49419203987/43490000000000000000000000 : ℝ)*base65 + (10372708116403236093/2174500000000000000000000000000000 : ℝ)*base67 + (3979306855572763907/2174500000000000000000000000000000 : ℝ)*base70 + (22051093172974763907/2174500000000000000000000000000000 : ℝ)*base72 + (17424053597283/4349000000000000000000000000 : ℝ)*base74 + (117602712033190763907/2174500000000000000000000000000000 : ℝ)*base76 + (5178831085345263907/2174500000000000000000000000000000 : ℝ)*base78 + (13643257917795236093/2174500000000000000000000000000000 : ℝ)*base79 + (628359849937/434900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (827081/125000000000000000000 : ℝ)*base90 + (827081/125000000000000000000 : ℝ)*base92 + (827081/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1576_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1576_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1576_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1576_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1576_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1576_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4649/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4212767/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1576_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
