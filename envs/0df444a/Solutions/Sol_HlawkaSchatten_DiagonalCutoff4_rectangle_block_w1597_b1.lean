-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:23.222464+00:00
-- url     : https://prove2.me/submissions/20cf683b-6c04-4795-a970-0403ffcce4f7

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
theorem support_rectangle_w1597_s3_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1737391717/10000000000 : ℝ)*x 0 + (5464298811/10000000000 : ℝ)*x 1 + (1035747739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1737391717/10000000000 : ℝ)^4707 ≤ (10679804831263/100000000000000 : ℝ)^3683 := by
    have hnat : (1737391717 : ℕ)^4707*100000000000000^3683 ≤ 10679804831263^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737391717 10000000000 10679804831263 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464298811/10000000000 : ℝ)^4707 ≤ (9238256817961/20000000000000 : ℝ)^3683 := by
    have hnat : (5464298811 : ℕ)^4707*20000000000000^3683 ≤ 9238256817961^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464298811 10000000000 9238256817961 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035747739/2000000000 : ℝ)^4707 ≤ (10782227765473/25000000000000 : ℝ)^3683 := by
    have hnat : (1035747739 : ℕ)^4707*25000000000000^3683 ≤ 10782227765473^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035747739 2000000000 10782227765473 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1737391717/10000000000 : ℝ), (5464298811/10000000000 : ℝ), (1035747739/2000000000 : ℝ)] ![(10679804831263/100000000000000 : ℝ), (9238256817961/20000000000000 : ℝ), (10782227765473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1737391717/10000000000 : ℝ)|^4707 ≤ (10679804831263/100000000000000 : ℝ)^3683
        have hw : |(-1737391717/10000000000 : ℝ)|=(1737391717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464298811/10000000000 : ℝ)|^4707 ≤ (9238256817961/20000000000000 : ℝ)^3683
        have hw : |(5464298811/10000000000 : ℝ)|=(5464298811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035747739/2000000000 : ℝ)|^4707 ≤ (10782227765473/25000000000000 : ℝ)^3683
        have hw : |(1035747739/2000000000 : ℝ)|=(1035747739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669450153/1250000000 : ℝ)*x 0 + (-18847521/100000000 : ℝ)*x 1 + (5178738597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669450153/1250000000 : ℝ)^4707 ≤ (4502022310367/10000000000000 : ℝ)^3683 := by
    have hnat : (669450153 : ℕ)^4707*10000000000000^3683 ≤ 4502022310367^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669450153 1250000000 4502022310367 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18847521/100000000 : ℝ)^4707 ≤ (5925433429769/50000000000000 : ℝ)^3683 := by
    have hnat : (18847521 : ℕ)^4707*50000000000000^3683 ≤ 5925433429769^3683*100000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18847521 100000000 5925433429769 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178738597/10000000000 : ℝ)^4707 ≤ (43128910018823/100000000000000 : ℝ)^3683 := by
    have hnat : (5178738597 : ℕ)^4707*100000000000000^3683 ≤ 43128910018823^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178738597 10000000000 43128910018823 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669450153/1250000000 : ℝ), (-18847521/100000000 : ℝ), (5178738597/10000000000 : ℝ)] ![(4502022310367/10000000000000 : ℝ), (5925433429769/50000000000000 : ℝ), (43128910018823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669450153/1250000000 : ℝ)|^4707 ≤ (4502022310367/10000000000000 : ℝ)^3683
        have hw : |(669450153/1250000000 : ℝ)|=(669450153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18847521/100000000 : ℝ)|^4707 ≤ (5925433429769/50000000000000 : ℝ)^3683
        have hw : |(-18847521/100000000 : ℝ)|=(18847521/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178738597/10000000000 : ℝ)|^4707 ≤ (43128910018823/100000000000000 : ℝ)^3683
        have hw : |(5178738597/10000000000 : ℝ)|=(5178738597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355601091/10000000000 : ℝ)*x 0 + (5178738747/10000000000 : ℝ)*x 1 + (-1884752079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355601091/10000000000 : ℝ)^4707 ≤ (45020221674797/100000000000000 : ℝ)^3683 := by
    have hnat : (5355601091 : ℕ)^4707*100000000000000^3683 ≤ 45020221674797^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355601091 10000000000 45020221674797 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178738747/10000000000 : ℝ)^4707 ≤ (43128911615357/100000000000000 : ℝ)^3683 := by
    have hnat : (5178738747 : ℕ)^4707*100000000000000^3683 ≤ 43128911615357^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178738747 10000000000 43128911615357 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884752079/10000000000 : ℝ)^4707 ≤ (11850866690783/100000000000000 : ℝ)^3683 := by
    have hnat : (1884752079 : ℕ)^4707*100000000000000^3683 ≤ 11850866690783^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884752079 10000000000 11850866690783 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355601091/10000000000 : ℝ), (5178738747/10000000000 : ℝ), (-1884752079/10000000000 : ℝ)] ![(45020221674797/100000000000000 : ℝ), (43128911615357/100000000000000 : ℝ), (11850866690783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355601091/10000000000 : ℝ)|^4707 ≤ (45020221674797/100000000000000 : ℝ)^3683
        have hw : |(5355601091/10000000000 : ℝ)|=(5355601091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178738747/10000000000 : ℝ)|^4707 ≤ (43128911615357/100000000000000 : ℝ)^3683
        have hw : |(5178738747/10000000000 : ℝ)|=(5178738747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884752079/10000000000 : ℝ)|^4707 ≤ (11850866690783/100000000000000 : ℝ)^3683
        have hw : |(-1884752079/10000000000 : ℝ)|=(1884752079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263955349/625000000 : ℝ)*x 0 + (243092983/625000000 : ℝ)*x 1 + (4579209831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263955349/625000000 : ℝ)^4707 ≤ (8308229349477/25000000000000 : ℝ)^3683 := by
    have hnat : (263955349 : ℕ)^4707*25000000000000^3683 ≤ 8308229349477^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263955349 625000000 8308229349477 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243092983/625000000 : ℝ)^4707 ≤ (14956792491127/50000000000000 : ℝ)^3683 := by
    have hnat : (243092983 : ℕ)^4707*50000000000000^3683 ≤ 14956792491127^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243092983 625000000 14956792491127 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579209831/10000000000 : ℝ)^4707 ≤ (18426748797869/50000000000000 : ℝ)^3683 := by
    have hnat : (4579209831 : ℕ)^4707*50000000000000^3683 ≤ 18426748797869^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579209831 10000000000 18426748797869 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263955349/625000000 : ℝ), (243092983/625000000 : ℝ), (4579209831/10000000000 : ℝ)] ![(8308229349477/25000000000000 : ℝ), (14956792491127/50000000000000 : ℝ), (18426748797869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263955349/625000000 : ℝ)|^4707 ≤ (8308229349477/25000000000000 : ℝ)^3683
        have hw : |(263955349/625000000 : ℝ)|=(263955349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243092983/625000000 : ℝ)|^4707 ≤ (14956792491127/50000000000000 : ℝ)^3683
        have hw : |(243092983/625000000 : ℝ)|=(243092983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579209831/10000000000 : ℝ)|^4707 ≤ (18426748797869/50000000000000 : ℝ)^3683
        have hw : |(4579209831/10000000000 : ℝ)|=(4579209831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1737465467/10000000000 : ℝ)*x 0 + (1036172037/2000000000 : ℝ)*x 1 + (8534617/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1737465467/10000000000 : ℝ)^4707 ≤ (10680384223453/100000000000000 : ℝ)^3683 := by
    have hnat : (1737465467 : ℕ)^4707*100000000000000^3683 ≤ 10680384223453^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737465467 10000000000 10680384223453 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036172037/2000000000 : ℝ)^4707 ≤ (8630298511397/20000000000000 : ℝ)^3683 := by
    have hnat : (1036172037 : ℕ)^4707*20000000000000^3683 ≤ 8630298511397^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036172037 2000000000 8630298511397 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8534617/15625000 : ℝ)^4707 ≤ (46168123202807/100000000000000 : ℝ)^3683 := by
    have hnat : (8534617 : ℕ)^4707*100000000000000^3683 ≤ 46168123202807^3683*15625000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8534617 15625000 46168123202807 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1737465467/10000000000 : ℝ), (1036172037/2000000000 : ℝ), (8534617/15625000 : ℝ)] ![(10680384223453/100000000000000 : ℝ), (8630298511397/20000000000000 : ℝ), (46168123202807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1737465467/10000000000 : ℝ)|^4707 ≤ (10680384223453/100000000000000 : ℝ)^3683
        have hw : |(-1737465467/10000000000 : ℝ)|=(1737465467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036172037/2000000000 : ℝ)|^4707 ≤ (8630298511397/20000000000000 : ℝ)^3683
        have hw : |(1036172037/2000000000 : ℝ)|=(1036172037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8534617/15625000 : ℝ)|^4707 ≤ (46168123202807/100000000000000 : ℝ)^3683
        have hw : |(8534617/15625000 : ℝ)|=(8534617/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279950641/10000000000 : ℝ)*x 0 + (-1601335993/10000000000 : ℝ)*x 1 + (218486191/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279950641/10000000000 : ℝ)^4707 ≤ (5526134974367/12500000000000 : ℝ)^3683 := by
    have hnat : (5279950641 : ℕ)^4707*12500000000000^3683 ≤ 5526134974367^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279950641 10000000000 5526134974367 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1601335993/10000000000 : ℝ)^4707 ≤ (37589055189/390625000000 : ℝ)^3683 := by
    have hnat : (1601335993 : ℕ)^4707*390625000000^3683 ≤ 37589055189^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601335993 10000000000 37589055189 390625000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218486191/400000000 : ℝ)^4707 ≤ (23084061034277/50000000000000 : ℝ)^3683 := by
    have hnat : (218486191 : ℕ)^4707*50000000000000^3683 ≤ 23084061034277^3683*400000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218486191 400000000 23084061034277 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279950641/10000000000 : ℝ), (-1601335993/10000000000 : ℝ), (218486191/400000000 : ℝ)] ![(5526134974367/12500000000000 : ℝ), (37589055189/390625000000 : ℝ), (23084061034277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279950641/10000000000 : ℝ)|^4707 ≤ (5526134974367/12500000000000 : ℝ)^3683
        have hw : |(5279950641/10000000000 : ℝ)|=(5279950641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1601335993/10000000000 : ℝ)|^4707 ≤ (37589055189/390625000000 : ℝ)^3683
        have hw : |(-1601335993/10000000000 : ℝ)|=(1601335993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218486191/400000000 : ℝ)|^4707 ≤ (23084061034277/50000000000000 : ℝ)^3683
        have hw : |(218486191/400000000 : ℝ)|=(218486191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319987707/2500000000 : ℝ)*x 0 + (5462154771/10000000000 : ℝ)*x 1 + (-1601335737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319987707/2500000000 : ℝ)^4707 ≤ (22104540898011/50000000000000 : ℝ)^3683 := by
    have hnat : (1319987707 : ℕ)^4707*50000000000000^3683 ≤ 22104540898011^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319987707 2500000000 22104540898011 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462154771/10000000000 : ℝ)^4707 ≤ (360688453323/781250000000 : ℝ)^3683 := by
    have hnat : (5462154771 : ℕ)^4707*781250000000^3683 ≤ 360688453323^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462154771 10000000000 360688453323 781250000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1601335737/10000000000 : ℝ)^4707 ≤ (37589047509/390625000000 : ℝ)^3683 := by
    have hnat : (1601335737 : ℕ)^4707*390625000000^3683 ≤ 37589047509^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601335737 10000000000 37589047509 390625000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319987707/2500000000 : ℝ), (5462154771/10000000000 : ℝ), (-1601335737/10000000000 : ℝ)] ![(22104540898011/50000000000000 : ℝ), (360688453323/781250000000 : ℝ), (37589047509/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319987707/2500000000 : ℝ)|^4707 ≤ (22104540898011/50000000000000 : ℝ)^3683
        have hw : |(1319987707/2500000000 : ℝ)|=(1319987707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462154771/10000000000 : ℝ)|^4707 ≤ (360688453323/781250000000 : ℝ)^3683
        have hw : |(5462154771/10000000000 : ℝ)|=(5462154771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1601335737/10000000000 : ℝ)|^4707 ≤ (37589047509/390625000000 : ℝ)^3683
        have hw : |(-1601335737/10000000000 : ℝ)|=(1601335737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s3_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223463679/10000000000 : ℝ)*x 0 + (4574085819/10000000000 : ℝ)*x 1 + (3894665661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223463679/10000000000 : ℝ)^4707 ≤ (1329388339081/4000000000000 : ℝ)^3683 := by
    have hnat : (4223463679 : ℕ)^4707*4000000000000^3683 ≤ 1329388339081^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223463679 10000000000 1329388339081 4000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574085819/10000000000 : ℝ)^4707 ≤ (36800802135319/100000000000000 : ℝ)^3683 := by
    have hnat : (4574085819 : ℕ)^4707*100000000000000^3683 ≤ 36800802135319^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574085819 10000000000 36800802135319 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3894665661/10000000000 : ℝ)^4707 ≤ (14982244690109/50000000000000 : ℝ)^3683 := by
    have hnat : (3894665661 : ℕ)^4707*50000000000000^3683 ≤ 14982244690109^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894665661 10000000000 14982244690109 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223463679/10000000000 : ℝ), (4574085819/10000000000 : ℝ), (3894665661/10000000000 : ℝ)] ![(1329388339081/4000000000000 : ℝ), (36800802135319/100000000000000 : ℝ), (14982244690109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223463679/10000000000 : ℝ)|^4707 ≤ (1329388339081/4000000000000 : ℝ)^3683
        have hw : |(4223463679/10000000000 : ℝ)|=(4223463679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574085819/10000000000 : ℝ)|^4707 ≤ (36800802135319/100000000000000 : ℝ)^3683
        have hw : |(4574085819/10000000000 : ℝ)|=(4574085819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3894665661/10000000000 : ℝ)|^4707 ≤ (14982244690109/50000000000000 : ℝ)^3683
        have hw : |(3894665661/10000000000 : ℝ)|=(3894665661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (819/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2069/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (318/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2069/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (318/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2069/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (318/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2069/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (318/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2069/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (318/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2069/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (318/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (318/3125 : ℝ) ^ (4703/1024 : ℝ) ≤ (1383555109837873/50000000000000000000 : ℝ) := by
    have hpowers : (318/3125 : ℝ)^4703 ≤ (1383555109837873/50000000000000000000 : ℝ)^1024 := by
      have hnat : (318 : ℕ)^4703*50000000000000000000^1024 ≤ 1383555109837873^1024*3125^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        318 3125 1383555109837873 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (318/3125 : ℝ)) (X := (1383555109837873/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2069/12500 : ℝ) ^ (4703/1024 : ℝ) ≤ (6460962669279339/25000000000000000000 : ℝ) := by
    have hpowers : (2069/12500 : ℝ)^4703 ≤ (6460962669279339/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2069 : ℕ)^4703*25000000000000000000^1024 ≤ 6460962669279339^1024*12500^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2069 12500 6460962669279339 25000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2069/12500 : ℝ)) (X := (6460962669279339/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001383555109837873/25000000000000000000 : ℝ) ≤ (10000120495833811/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25001383555109837873/25000000000000000000 : ℝ)^1024 ≤ (10000120495833811/10000000000000000 : ℝ)^4703 := by
      have hnat : (25001383555109837873 : ℕ)^1024*10000000000000000^4703 ≤ 10000120495833811^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001383555109837873 25000000000000000000 10000120495833811 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000120495833811/10000000000000000 : ℝ)) (X := (25001383555109837873/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014305480448396551/50000000000000000000 : ℝ) ≤ (10000622886368409/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (50014305480448396551/50000000000000000000 : ℝ)^1024 ≤ (10000622886368409/10000000000000000 : ℝ)^4703 := by
      have hnat : (50014305480448396551 : ℕ)^1024*10000000000000000^4703 ≤ 10000622886368409^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014305480448396551 50000000000000000000 10000622886368409 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622886368409/10000000000000000 : ℝ)) (X := (50014305480448396551/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506460962669279339/12500000000000000000 : ℝ) ≤ (10001125276903007/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (12506460962669279339/12500000000000000000 : ℝ)^1024 ≤ (10001125276903007/10000000000000000 : ℝ)^4703 := by
      have hnat : (12506460962669279339 : ℕ)^1024*10000000000000000^4703 ≤ 10001125276903007^4703*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506460962669279339 12500000000000000000 10001125276903007 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001125276903007/10000000000000000 : ℝ)) (X := (12506460962669279339/12500000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1383555109837873/50000000000000000000 : ℝ) ≤ ((1593763590731906011/1594000000000000000 : ℝ)+2*(251195267299/318800000000000 : ℝ)*(318/3125 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (1593763590731906011/1594000000000000000 : ℝ)+2*(251195267299/318800000000000 : ℝ)*(318/3125 : ℝ)=(10000120495833811/10000000000000000 : ℝ) by norm_num, show 1+2*(1383555109837873/50000000000000000000 : ℝ)=(25001383555109837873/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6460962669279339/25000000000000000000 : ℝ)+(1383555109837873/50000000000000000000 : ℝ) ≤ ((1593763590731906011/1594000000000000000 : ℝ)+(251195267299/318800000000000 : ℝ)*((2069/12500 : ℝ)+(318/3125 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (1593763590731906011/1594000000000000000 : ℝ)+(251195267299/318800000000000 : ℝ)*((2069/12500 : ℝ)+(318/3125 : ℝ))=(10000622886368409/10000000000000000 : ℝ) by norm_num, show 1+(6460962669279339/25000000000000000000 : ℝ)+(1383555109837873/50000000000000000000 : ℝ)=(50014305480448396551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6460962669279339/25000000000000000000 : ℝ) ≤ ((1593763590731906011/1594000000000000000 : ℝ)+2*(251195267299/318800000000000 : ℝ)*(2069/12500 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (1593763590731906011/1594000000000000000 : ℝ)+2*(251195267299/318800000000000 : ℝ)*(2069/12500 : ℝ)=(10001125276903007/10000000000000000 : ℝ) by norm_num, show 1+2*(6460962669279339/25000000000000000000 : ℝ)=(12506460962669279339/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1593763590731906011/1594000000000000000 : ℝ)*(X 1 0+X 2 0)+(251195267299/318800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (318/3125 : ℝ)) (hi := (2069/12500 : ℝ)) (c := (1593763590731906011/1594000000000000000 : ℝ)) (alpha := (251195267299/318800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1593763590731906011/1594000000000000000 : ℝ)*(X 0 1+X 2 1)+(251195267299/318800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (318/3125 : ℝ)) (hi := (2069/12500 : ℝ)) (c := (1593763590731906011/1594000000000000000 : ℝ)) (alpha := (251195267299/318800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1593763590731906011/1594000000000000000 : ℝ)*(X 0 2+X 1 2)+(251195267299/318800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (318/3125 : ℝ)) (hi := (2069/12500 : ℝ)) (c := (1593763590731906011/1594000000000000000 : ℝ)) (alpha := (251195267299/318800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1737391717/10000000000 : ℝ)*X 0 0+(5464298811/10000000000 : ℝ)*X 0 1+(1035747739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669450153/1250000000 : ℝ)*X 1 0+(-18847521/100000000 : ℝ)*X 1 1+(5178738597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355601091/10000000000 : ℝ)*X 2 0+(5178738747/10000000000 : ℝ)*X 2 1+(-1884752079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((263955349/625000000 : ℝ)*X 0 0+(243092983/625000000 : ℝ)*X 0 1+(4579209831/10000000000 : ℝ)*X 0 2+(263955349/625000000 : ℝ)*X 1 0+(243092983/625000000 : ℝ)*X 1 1+(4579209831/10000000000 : ℝ)*X 1 2+(263955349/625000000 : ℝ)*X 2 0+(243092983/625000000 : ℝ)*X 2 1+(4579209831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1737465467/10000000000 : ℝ)*X 0 0+(1036172037/2000000000 : ℝ)*X 0 1+(8534617/15625000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279950641/10000000000 : ℝ)*X 1 0+(-1601335993/10000000000 : ℝ)*X 1 1+(218486191/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319987707/2500000000 : ℝ)*X 2 0+(5462154771/10000000000 : ℝ)*X 2 1+(-1601335737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4223463679/10000000000 : ℝ)*X 0 0+(4574085819/10000000000 : ℝ)*X 0 1+(3894665661/10000000000 : ℝ)*X 0 2+(4223463679/10000000000 : ℝ)*X 1 0+(4574085819/10000000000 : ℝ)*X 1 1+(3894665661/10000000000 : ℝ)*X 1 2+(4223463679/10000000000 : ℝ)*X 2 0+(4574085819/10000000000 : ℝ)*X 2 1+(3894665661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25817529262204539715152579/9962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555906941/100000000000000 : ℝ)*(base19) + (219262551/50000000000000 : ℝ)*(base23) + (4072433/25000000000000 : ℝ)*(lower2) + (219703/400000000000 : ℝ)*(upper3) + (1373703/4000000000000 : ℝ)*(upper5) + (618970970433063/25000000000000 : ℝ)*(major0) + (618970970433063/25000000000000 : ℝ)*(major1) + (618970970433063/25000000000000 : ℝ)*(major2) + (437737048831849/12500000000000 : ℝ)*(sp0) + (3501902142534091/100000000000000 : ℝ)*(sp1) + (350190225991593/10000000000000 : ℝ)*(sp2) + (1449862071514111/100000000000000 : ℝ)*(sp3) + (6307786239/100000000000000 : ℝ)*(sp4) + (290712699/10000000000000 : ℝ)*(sp7) + (1449864978641101/100000000000000 : ℝ)*(f.failure) + (437737837305129/12500000000000 : ℝ)*(f.sum) + (210837177363/249062500000000000000000000 : ℝ)*base66 + (51554357488776693/39850000000000000000000000000000 : ℝ)*base67 + (53779443764323307/39850000000000000000000000000000 : ℝ)*base70 + (355516113190273307/39850000000000000000000000000000 : ℝ)*base72 + (14425057887607/3985000000000000000000000000 : ℝ)*base73 + (347941685809273307/39850000000000000000000000000000 : ℝ)*base76 + (357705960193373307/39850000000000000000000000000000 : ℝ)*base78 + (310701795853773307/39850000000000000000000000000000 : ℝ)*base80 + (3544144655063/996250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (37445957/5000000000000000000000 : ℝ)*base89 + (37445957/5000000000000000000000 : ℝ)*base91 + (37445957/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76491124513365170585176803/19925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833644859/100000000000000 : ℝ)*(base19) + (26701671/2500000000000 : ℝ)*(base23) + (33008953/25000000000000 : ℝ)*(upper3) + (18288353/100000000000000 : ℝ)*(lower4) + (29688081/50000000000000 : ℝ)*(upper5) + (628354215094103/25000000000000 : ℝ)*(major0) + (628354215094103/25000000000000 : ℝ)*(major1) + (628354215094103/25000000000000 : ℝ)*(major2) + (3685956361/50000000000000 : ℝ)*(sp1) + (1566021693/12500000000000 : ℝ)*(sp2) + (710997898640499/20000000000000 : ℝ)*(sp4) + (1777490643822457/50000000000000 : ℝ)*(sp5) + (355497589696211/10000000000000 : ℝ)*(sp6) + (294368819917049/20000000000000 : ℝ)*(sp7) + (294368819917049/20000000000000 : ℝ)*(f.failure) + (710997898640499/20000000000000 : ℝ)*(f.sum) + (7533035020647/3985000000000000000000000000 : ℝ)*base65 + (304526145239838133/39850000000000000000000000000000 : ℝ)*base67 + (57269036937088133/39850000000000000000000000000000 : ℝ)*base69 + (63872962518888133/39850000000000000000000000000000 : ℝ)*base71 + (1163891203037/249062500000000000000000000 : ℝ)*base73 + (146777326044688133/39850000000000000000000000000000 : ℝ)*base75 + (78067453536188133/39850000000000000000000000000000 : ℝ)*base77 + (284295312310288133/39850000000000000000000000000000 : ℝ)*base79 + (3243043112359/1992500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6551407/1000000000000000000000 : ℝ)*base90 + (6551407/1000000000000000000000 : ℝ)*base92 + (6551407/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1597_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (819/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1597_s4_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868774257/5000000000 : ℝ)*x 0 + (2731756277/5000000000 : ℝ)*x 1 + (517942101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868774257/5000000000 : ℝ)^4707 ≤ (2670259165649/25000000000000 : ℝ)^3683 := by
    have hnat : (868774257 : ℕ)^4707*25000000000000^3683 ≤ 2670259165649^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868774257 5000000000 2670259165649 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731756277/5000000000 : ℝ)^4707 ≤ (23091394930923/50000000000000 : ℝ)^3683 := by
    have hnat : (2731756277 : ℕ)^4707*50000000000000^3683 ≤ 23091394930923^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731756277 5000000000 23091394930923 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517942101/1000000000 : ℝ)^4707 ≤ (43136173456573/100000000000000 : ℝ)^3683 := by
    have hnat : (517942101 : ℕ)^4707*100000000000000^3683 ≤ 43136173456573^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517942101 1000000000 43136173456573 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868774257/5000000000 : ℝ), (2731756277/5000000000 : ℝ), (517942101/1000000000 : ℝ)] ![(2670259165649/25000000000000 : ℝ), (23091394930923/50000000000000 : ℝ), (43136173456573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868774257/5000000000 : ℝ)|^4707 ≤ (2670259165649/25000000000000 : ℝ)^3683
        have hw : |(-868774257/5000000000 : ℝ)|=(868774257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731756277/5000000000 : ℝ)|^4707 ≤ (23091394930923/50000000000000 : ℝ)^3683
        have hw : |(2731756277/5000000000 : ℝ)|=(2731756277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517942101/1000000000 : ℝ)|^4707 ≤ (43136173456573/100000000000000 : ℝ)^3683
        have hw : |(517942101/1000000000 : ℝ)|=(517942101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677695683/5000000000 : ℝ)*x 0 + (-471032181/2500000000 : ℝ)*x 1 + (5179421043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677695683/5000000000 : ℝ)^4707 ≤ (9003593705353/20000000000000 : ℝ)^3683 := by
    have hnat : (2677695683 : ℕ)^4707*20000000000000^3683 ≤ 9003593705353^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677695683 5000000000 9003593705353 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471032181/2500000000 : ℝ)^4707 ≤ (11845857658409/100000000000000 : ℝ)^3683 := by
    have hnat : (471032181 : ℕ)^4707*100000000000000^3683 ≤ 11845857658409^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471032181 2500000000 11845857658409 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179421043/10000000000 : ℝ)^4707 ≤ (43136173807823/100000000000000 : ℝ)^3683 := by
    have hnat : (5179421043 : ℕ)^4707*100000000000000^3683 ≤ 43136173807823^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179421043 10000000000 43136173807823 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677695683/5000000000 : ℝ), (-471032181/2500000000 : ℝ), (5179421043/10000000000 : ℝ)] ![(9003593705353/20000000000000 : ℝ), (11845857658409/100000000000000 : ℝ), (43136173807823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677695683/5000000000 : ℝ)|^4707 ≤ (9003593705353/20000000000000 : ℝ)^3683
        have hw : |(2677695683/5000000000 : ℝ)|=(2677695683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471032181/2500000000 : ℝ)|^4707 ≤ (11845857658409/100000000000000 : ℝ)^3683
        have hw : |(-471032181/2500000000 : ℝ)|=(471032181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179421043/10000000000 : ℝ)|^4707 ≤ (43136173807823/100000000000000 : ℝ)^3683
        have hw : |(5179421043/10000000000 : ℝ)|=(5179421043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355391579/10000000000 : ℝ)*x 0 + (1294855207/2500000000 : ℝ)*x 1 + (-1884128723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355391579/10000000000 : ℝ)^4707 ≤ (9003594163017/20000000000000 : ℝ)^3683 := by
    have hnat : (5355391579 : ℕ)^4707*20000000000000^3683 ≤ 9003594163017^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355391579 10000000000 9003594163017 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294855207/2500000000 : ℝ)^4707 ≤ (21568085759687/50000000000000 : ℝ)^3683 := by
    have hnat : (1294855207 : ℕ)^4707*50000000000000^3683 ≤ 21568085759687^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294855207 2500000000 21568085759687 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884128723/10000000000 : ℝ)^4707 ≤ (5922928825187/50000000000000 : ℝ)^3683 := by
    have hnat : (1884128723 : ℕ)^4707*50000000000000^3683 ≤ 5922928825187^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884128723 10000000000 5922928825187 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355391579/10000000000 : ℝ), (1294855207/2500000000 : ℝ), (-1884128723/10000000000 : ℝ)] ![(9003594163017/20000000000000 : ℝ), (21568085759687/50000000000000 : ℝ), (5922928825187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355391579/10000000000 : ℝ)|^4707 ≤ (9003594163017/20000000000000 : ℝ)^3683
        have hw : |(5355391579/10000000000 : ℝ)|=(5355391579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294855207/2500000000 : ℝ)|^4707 ≤ (21568085759687/50000000000000 : ℝ)^3683
        have hw : |(1294855207/2500000000 : ℝ)|=(1294855207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884128723/10000000000 : ℝ)|^4707 ≤ (5922928825187/50000000000000 : ℝ)^3683
        have hw : |(-1884128723/10000000000 : ℝ)|=(1884128723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223388243/10000000000 : ℝ)*x 0 + (121601629/312500000 : ℝ)*x 1 + (4577423147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223388243/10000000000 : ℝ)^4707 ≤ (16616974912027/50000000000000 : ℝ)^3683 := by
    have hnat : (4223388243 : ℕ)^4707*50000000000000^3683 ≤ 16616974912027^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223388243 10000000000 16616974912027 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121601629/312500000 : ℝ)^4707 ≤ (29930928730903/100000000000000 : ℝ)^3683 := by
    have hnat : (121601629 : ℕ)^4707*100000000000000^3683 ≤ 29930928730903^3683*312500000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121601629 312500000 29930928730903 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577423147/10000000000 : ℝ)^4707 ≤ (36835121432717/100000000000000 : ℝ)^3683 := by
    have hnat : (4577423147 : ℕ)^4707*100000000000000^3683 ≤ 36835121432717^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577423147 10000000000 36835121432717 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223388243/10000000000 : ℝ), (121601629/312500000 : ℝ), (4577423147/10000000000 : ℝ)] ![(16616974912027/50000000000000 : ℝ), (29930928730903/100000000000000 : ℝ), (36835121432717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223388243/10000000000 : ℝ)|^4707 ≤ (16616974912027/50000000000000 : ℝ)^3683
        have hw : |(4223388243/10000000000 : ℝ)|=(4223388243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121601629/312500000 : ℝ)|^4707 ≤ (29930928730903/100000000000000 : ℝ)^3683
        have hw : |(121601629/312500000 : ℝ)|=(121601629/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577423147/10000000000 : ℝ)|^4707 ≤ (36835121432717/100000000000000 : ℝ)^3683
        have hw : |(4577423147/10000000000 : ℝ)|=(4577423147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868810847/5000000000 : ℝ)*x 0 + (323845053/625000000 : ℝ)*x 1 + (5461390211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868810847/5000000000 : ℝ)^4707 ≤ (1068161159117/10000000000000 : ℝ)^3683 := by
    have hnat : (868810847 : ℕ)^4707*10000000000000^3683 ≤ 1068161159117^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868810847 5000000000 1068161159117 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323845053/625000000 : ℝ)^4707 ≤ (43158525289717/100000000000000 : ℝ)^3683 := by
    have hnat : (323845053 : ℕ)^4707*100000000000000^3683 ≤ 43158525289717^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323845053 625000000 43158525289717 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461390211/10000000000 : ℝ)^4707 ≤ (23079931547449/50000000000000 : ℝ)^3683 := by
    have hnat : (5461390211 : ℕ)^4707*50000000000000^3683 ≤ 23079931547449^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461390211 10000000000 23079931547449 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868810847/5000000000 : ℝ), (323845053/625000000 : ℝ), (5461390211/10000000000 : ℝ)] ![(1068161159117/10000000000000 : ℝ), (43158525289717/100000000000000 : ℝ), (23079931547449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868810847/5000000000 : ℝ)|^4707 ≤ (1068161159117/10000000000000 : ℝ)^3683
        have hw : |(-868810847/5000000000 : ℝ)|=(868810847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323845053/625000000 : ℝ)|^4707 ≤ (43158525289717/100000000000000 : ℝ)^3683
        have hw : |(323845053/625000000 : ℝ)|=(323845053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461390211/10000000000 : ℝ)|^4707 ≤ (23079931547449/50000000000000 : ℝ)^3683
        have hw : |(5461390211/10000000000 : ℝ)|=(5461390211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528013181/1000000000 : ℝ)*x 0 + (-10013493/62500000 : ℝ)*x 1 + (2730695107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528013181/1000000000 : ℝ)^4707 ≤ (44211018492439/100000000000000 : ℝ)^3683 := by
    have hnat : (528013181 : ℕ)^4707*100000000000000^3683 ≤ 44211018492439^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528013181 1000000000 44211018492439 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10013493/62500000 : ℝ)^4707 ≤ (9629118354419/100000000000000 : ℝ)^3683 := by
    have hnat : (10013493 : ℕ)^4707*100000000000000^3683 ≤ 9629118354419^3683*62500000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10013493 62500000 9629118354419 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730695107/5000000000 : ℝ)^4707 ≤ (5769982890913/12500000000000 : ℝ)^3683 := by
    have hnat : (2730695107 : ℕ)^4707*12500000000000^3683 ≤ 5769982890913^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730695107 5000000000 5769982890913 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528013181/1000000000 : ℝ), (-10013493/62500000 : ℝ), (2730695107/5000000000 : ℝ)] ![(44211018492439/100000000000000 : ℝ), (9629118354419/100000000000000 : ℝ), (5769982890913/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528013181/1000000000 : ℝ)|^4707 ≤ (44211018492439/100000000000000 : ℝ)^3683
        have hw : |(528013181/1000000000 : ℝ)|=(528013181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10013493/62500000 : ℝ)|^4707 ≤ (9629118354419/100000000000000 : ℝ)^3683
        have hw : |(-10013493/62500000 : ℝ)|=(10013493/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730695107/5000000000 : ℝ)|^4707 ≤ (5769982890913/12500000000000 : ℝ)^3683
        have hw : |(2730695107/5000000000 : ℝ)|=(2730695107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528013181/1000000000 : ℝ)*x 0 + (5461390213/10000000000 : ℝ)*x 1 + (-1602158883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528013181/1000000000 : ℝ)^4707 ≤ (44211018492439/100000000000000 : ℝ)^3683 := by
    have hnat : (528013181 : ℕ)^4707*100000000000000^3683 ≤ 44211018492439^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528013181 1000000000 44211018492439 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461390213/10000000000 : ℝ)^4707 ≤ (23079931558251/50000000000000 : ℝ)^3683 := by
    have hnat : (5461390213 : ℕ)^4707*50000000000000^3683 ≤ 23079931558251^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461390213 10000000000 23079931558251 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602158883/10000000000 : ℝ)^4707 ≤ (4814559188731/50000000000000 : ℝ)^3683 := by
    have hnat : (1602158883 : ℕ)^4707*50000000000000^3683 ≤ 4814559188731^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602158883 10000000000 4814559188731 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528013181/1000000000 : ℝ), (5461390213/10000000000 : ℝ), (-1602158883/10000000000 : ℝ)] ![(44211018492439/100000000000000 : ℝ), (23079931558251/50000000000000 : ℝ), (4814559188731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528013181/1000000000 : ℝ)|^4707 ≤ (44211018492439/100000000000000 : ℝ)^3683
        have hw : |(528013181/1000000000 : ℝ)|=(528013181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461390213/10000000000 : ℝ)|^4707 ≤ (23079931558251/50000000000000 : ℝ)^3683
        have hw : |(5461390213/10000000000 : ℝ)|=(5461390213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1602158883/10000000000 : ℝ)|^4707 ≤ (4814559188731/50000000000000 : ℝ)^3683
        have hw : |(-1602158883/10000000000 : ℝ)|=(1602158883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s4_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2111781639/5000000000 : ℝ)*x 0 + (4572352797/10000000000 : ℝ)*x 1 + (3896375851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111781639/5000000000 : ℝ)^4707 ≤ (16617855070427/50000000000000 : ℝ)^3683 := by
    have hnat : (2111781639 : ℕ)^4707*50000000000000^3683 ≤ 16617855070427^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111781639 5000000000 16617855070427 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572352797/10000000000 : ℝ)^4707 ≤ (36782983409121/100000000000000 : ℝ)^3683 := by
    have hnat : (4572352797 : ℕ)^4707*100000000000000^3683 ≤ 36782983409121^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572352797 10000000000 36782983409121 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3896375851/10000000000 : ℝ)^4707 ≤ (374766330491/1250000000000 : ℝ)^3683 := by
    have hnat : (3896375851 : ℕ)^4707*1250000000000^3683 ≤ 374766330491^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896375851 10000000000 374766330491 1250000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2111781639/5000000000 : ℝ), (4572352797/10000000000 : ℝ), (3896375851/10000000000 : ℝ)] ![(16617855070427/50000000000000 : ℝ), (36782983409121/100000000000000 : ℝ), (374766330491/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2111781639/5000000000 : ℝ)|^4707 ≤ (16617855070427/50000000000000 : ℝ)^3683
        have hw : |(2111781639/5000000000 : ℝ)|=(2111781639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572352797/10000000000 : ℝ)|^4707 ≤ (36782983409121/100000000000000 : ℝ)^3683
        have hw : |(4572352797/10000000000 : ℝ)|=(4572352797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3896375851/10000000000 : ℝ)|^4707 ≤ (374766330491/1250000000000 : ℝ)^3683
        have hw : |(3896375851/10000000000 : ℝ)|=(3896375851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (819/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2069/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (819/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (819/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (819/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (819/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (819/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (819/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10331/100000 : ℝ) ^ (4703/1024 : ℝ) ≤ (370756896336573/12500000000000000000 : ℝ) := by
    have hpowers : (10331/100000 : ℝ)^4703 ≤ (370756896336573/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10331 : ℕ)^4703*12500000000000000000^1024 ≤ 370756896336573^1024*100000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10331 100000 370756896336573 12500000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10331/100000 : ℝ)) (X := (370756896336573/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (819/5000 : ℝ) ^ (4703/1024 : ℝ) ≤ (12316625663673821/50000000000000000000 : ℝ) := by
    have hpowers : (819/5000 : ℝ)^4703 ≤ (12316625663673821/50000000000000000000 : ℝ)^1024 := by
      have hnat : (819 : ℕ)^4703*50000000000000000000^1024 ≤ 12316625663673821^1024*5000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        819 5000 12316625663673821 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (819/5000 : ℝ)) (X := (12316625663673821/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250370756896336573/6250000000000000000 : ℝ) ≤ (2000025831767177/2000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (6250370756896336573/6250000000000000000 : ℝ)^1024 ≤ (2000025831767177/2000000000000000 : ℝ)^4703 := by
      have hnat : (6250370756896336573 : ℕ)^1024*2000000000000000^4703 ≤ 2000025831767177^4703*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250370756896336573 6250000000000000000 2000025831767177 2000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000025831767177/2000000000000000 : ℝ)) (X := (6250370756896336573/6250000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013799653249020113/50000000000000000000 : ℝ) ≤ (5000300432059349/5000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (50013799653249020113/50000000000000000000 : ℝ)^1024 ≤ (5000300432059349/5000000000000000 : ℝ)^4703 := by
      have hnat : (50013799653249020113 : ℕ)^1024*5000000000000000^4703 ≤ 5000300432059349^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013799653249020113 50000000000000000000 5000300432059349 5000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000300432059349/5000000000000000 : ℝ)) (X := (50013799653249020113/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012316625663673821/25000000000000000000 : ℝ) ≤ (10001072569401511/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25012316625663673821/25000000000000000000 : ℝ)^1024 ≤ (10001072569401511/10000000000000000 : ℝ)^4703 := by
      have hnat : (25012316625663673821 : ℕ)^1024*10000000000000000^4703 ≤ 10001072569401511^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012316625663673821 25000000000000000000 10001072569401511 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072569401511/10000000000000000 : ℝ)) (X := (25012316625663673821/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(370756896336573/12500000000000000000 : ℝ) ≤ ((60481034907244786159/60490000000000000000 : ℝ)+2*(471705282813/604900000000000 : ℝ)*(10331/100000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (60481034907244786159/60490000000000000000 : ℝ)+2*(471705282813/604900000000000 : ℝ)*(10331/100000 : ℝ)=(2000025831767177/2000000000000000 : ℝ) by norm_num, show 1+2*(370756896336573/12500000000000000000 : ℝ)=(6250370756896336573/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12316625663673821/50000000000000000000 : ℝ)+(370756896336573/12500000000000000000 : ℝ) ≤ ((60481034907244786159/60490000000000000000 : ℝ)+(471705282813/604900000000000 : ℝ)*((819/5000 : ℝ)+(10331/100000 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (60481034907244786159/60490000000000000000 : ℝ)+(471705282813/604900000000000 : ℝ)*((819/5000 : ℝ)+(10331/100000 : ℝ))=(5000300432059349/5000000000000000 : ℝ) by norm_num, show 1+(12316625663673821/50000000000000000000 : ℝ)+(370756896336573/12500000000000000000 : ℝ)=(50013799653249020113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12316625663673821/50000000000000000000 : ℝ) ≤ ((60481034907244786159/60490000000000000000 : ℝ)+2*(471705282813/604900000000000 : ℝ)*(819/5000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (60481034907244786159/60490000000000000000 : ℝ)+2*(471705282813/604900000000000 : ℝ)*(819/5000 : ℝ)=(10001072569401511/10000000000000000 : ℝ) by norm_num, show 1+2*(12316625663673821/50000000000000000000 : ℝ)=(25012316625663673821/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60481034907244786159/60490000000000000000 : ℝ)*(X 1 0+X 2 0)+(471705282813/604900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (819/5000 : ℝ)) (c := (60481034907244786159/60490000000000000000 : ℝ)) (alpha := (471705282813/604900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60481034907244786159/60490000000000000000 : ℝ)*(X 0 1+X 2 1)+(471705282813/604900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (819/5000 : ℝ)) (c := (60481034907244786159/60490000000000000000 : ℝ)) (alpha := (471705282813/604900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60481034907244786159/60490000000000000000 : ℝ)*(X 0 2+X 1 2)+(471705282813/604900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (10331/100000 : ℝ)) (hi := (819/5000 : ℝ)) (c := (60481034907244786159/60490000000000000000 : ℝ)) (alpha := (471705282813/604900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-868774257/5000000000 : ℝ)*X 0 0+(2731756277/5000000000 : ℝ)*X 0 1+(517942101/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677695683/5000000000 : ℝ)*X 1 0+(-471032181/2500000000 : ℝ)*X 1 1+(5179421043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355391579/10000000000 : ℝ)*X 2 0+(1294855207/2500000000 : ℝ)*X 2 1+(-1884128723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4223388243/10000000000 : ℝ)*X 0 0+(121601629/312500000 : ℝ)*X 0 1+(4577423147/10000000000 : ℝ)*X 0 2+(4223388243/10000000000 : ℝ)*X 1 0+(121601629/312500000 : ℝ)*X 1 1+(4577423147/10000000000 : ℝ)*X 1 2+(4223388243/10000000000 : ℝ)*X 2 0+(121601629/312500000 : ℝ)*X 2 1+(4577423147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-868810847/5000000000 : ℝ)*X 0 0+(323845053/625000000 : ℝ)*X 0 1+(5461390211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528013181/1000000000 : ℝ)*X 1 0+(-10013493/62500000 : ℝ)*X 1 1+(2730695107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528013181/1000000000 : ℝ)*X 2 0+(5461390213/10000000000 : ℝ)*X 2 1+(-1602158883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2111781639/5000000000 : ℝ)*X 0 0+(4572352797/10000000000 : ℝ)*X 0 1+(3896375851/10000000000 : ℝ)*X 0 2+(2111781639/5000000000 : ℝ)*X 1 0+(4572352797/10000000000 : ℝ)*X 1 1+(3896375851/10000000000 : ℝ)*X 1 2+(2111781639/5000000000 : ℝ)*X 2 0+(4572352797/10000000000 : ℝ)*X 2 1+(3896375851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206533338403702899853037301/16437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67293741/6250000000000 : ℝ)*(base19) + (149741911/20000000000000 : ℝ)*(base23) + (143435703/50000000000000 : ℝ)*(lower2) + (322104453/100000000000000 : ℝ)*(upper3) + (2265223/6250000000000 : ℝ)*(lower4) + (311085765601801/12500000000000 : ℝ)*(major0) + (311085765601801/12500000000000 : ℝ)*(major1) + (311085765601801/12500000000000 : ℝ)*(major2) + (880000631980767/25000000000000 : ℝ)*(sp0) + (3520008847181551/100000000000000 : ℝ)*(sp1) + (880002293792963/25000000000000 : ℝ)*(sp2) + (91085022308369/6250000000000 : ℝ)*(sp3) + (7395958339/100000000000000 : ℝ)*(sp4) + (154998797/10000000000000 : ℝ)*(sp7) + (728680953460937/50000000000000 : ℝ)*(f.failure) + (55000155060647/1562500000000 : ℝ)*(f.sum) + (63452841441613/15122500000000000000000000000 : ℝ)*base66 + (2477539173732677641/756125000000000000000000000000000 : ℝ)*base68 + (3184839277838697359/756125000000000000000000000000000 : ℝ)*base69 + (715275724198822359/756125000000000000000000000000000 : ℝ)*base71 + (59220050122703/15122500000000000000000000000 : ℝ)*base74 + (1030261480499197359/756125000000000000000000000000000 : ℝ)*base75 + (398651675641572359/756125000000000000000000000000000 : ℝ)*base77 + (1491541823893677641/756125000000000000000000000000000 : ℝ)*base80 + (31903590056993/15122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (23331809/2500000000000000000000 : ℝ)*base89 + (23331809/2500000000000000000000 : ℝ)*base91 + (23331809/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13106340043073480857671662847/1512250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1347811867/100000000000000 : ℝ)*(base19) + (364667527/25000000000000 : ℝ)*(base23) + (21530919/5000000000000 : ℝ)*(lower1) + (182172757/100000000000000 : ℝ)*(upper3) + (2002563/4000000000000 : ℝ)*(lower4) + (44945959/25000000000000 : ℝ)*(upper5) + (1263103409394811/50000000000000 : ℝ)*(major0) + (1263103409394811/50000000000000 : ℝ)*(major1) + (1263103409394811/50000000000000 : ℝ)*(major2) + (1125506837/100000000000000 : ℝ)*(sp2) + (223317469666251/6250000000000 : ℝ)*(sp4) + (3573078166848149/100000000000000 : ℝ)*(sp5) + (3573076930483071/100000000000000 : ℝ)*(sp6) + (1479333834026513/100000000000000 : ℝ)*(sp7) + (1479333834026513/100000000000000 : ℝ)*(f.failure) + (223317469666251/6250000000000 : ℝ)*(f.sum) + (10832971318533/3780625000000000000000000000 : ℝ)*base66 + (22778009331876979051/3024500000000000000000000000000000 : ℝ)*base68 + (2148561764371979051/3024500000000000000000000000000000 : ℝ)*base70 + (21137764315685520949/3024500000000000000000000000000000 : ℝ)*base71 + (76459877670141/30245000000000000000000000000 : ℝ)*base73 + (4514077498133020949/3024500000000000000000000000000000 : ℝ)*base75 + (8671085977167979051/3024500000000000000000000000000000 : ℝ)*base78 + (36085118508856479051/3024500000000000000000000000000000 : ℝ)*base80 + (222156243560531/30245000000000000000000000000 : ℝ)*base81 + (4292841/5000000000000000000000 : ℝ)*base89 + (4292841/5000000000000000000000 : ℝ)*base91 + (4292841/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1597_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (819/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1597_s5_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1737563879/10000000000 : ℝ)*x 0 + (170732549/312500000 : ℝ)*x 1 + (5179481717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1737563879/10000000000 : ℝ)^4707 ≤ (10681157375041/100000000000000 : ℝ)^3683 := by
    have hnat : (1737563879 : ℕ)^4707*100000000000000^3683 ≤ 10681157375041^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737563879 10000000000 10681157375041 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170732549/312500000 : ℝ)^4707 ≤ (46182022990309/100000000000000 : ℝ)^3683 := by
    have hnat : (170732549 : ℕ)^4707*100000000000000^3683 ≤ 46182022990309^3683*312500000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170732549 312500000 46182022990309 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179481717/10000000000 : ℝ)^4707 ≤ (21568409809991/50000000000000 : ℝ)^3683 := by
    have hnat : (5179481717 : ℕ)^4707*50000000000000^3683 ≤ 21568409809991^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179481717 10000000000 21568409809991 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1737563879/10000000000 : ℝ), (170732549/312500000 : ℝ), (5179481717/10000000000 : ℝ)] ![(10681157375041/100000000000000 : ℝ), (46182022990309/100000000000000 : ℝ), (21568409809991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1737563879/10000000000 : ℝ)|^4707 ≤ (10681157375041/100000000000000 : ℝ)^3683
        have hw : |(-1737563879/10000000000 : ℝ)|=(1737563879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170732549/312500000 : ℝ)|^4707 ≤ (46182022990309/100000000000000 : ℝ)^3683
        have hw : |(170732549/312500000 : ℝ)|=(170732549/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179481717/10000000000 : ℝ)|^4707 ≤ (21568409809991/50000000000000 : ℝ)^3683
        have hw : |(5179481717/10000000000 : ℝ)|=(5179481717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071074577/2000000000 : ℝ)*x 0 + (-1884072879/10000000000 : ℝ)*x 1 + (5179481853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071074577/2000000000 : ℝ)^4707 ≤ (22508884990091/50000000000000 : ℝ)^3683 := by
    have hnat : (1071074577 : ℕ)^4707*50000000000000^3683 ≤ 22508884990091^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071074577 2000000000 22508884990091 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884072879/10000000000 : ℝ)^4707 ≤ (11845408932729/100000000000000 : ℝ)^3683 := by
    have hnat : (1884072879 : ℕ)^4707*100000000000000^3683 ≤ 11845408932729^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884072879 10000000000 11845408932729 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179481853/10000000000 : ℝ)^4707 ≤ (10784205266891/25000000000000 : ℝ)^3683 := by
    have hnat : (5179481853 : ℕ)^4707*25000000000000^3683 ≤ 10784205266891^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179481853 10000000000 10784205266891 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071074577/2000000000 : ℝ), (-1884072879/10000000000 : ℝ), (5179481853/10000000000 : ℝ)] ![(22508884990091/50000000000000 : ℝ), (11845408932729/100000000000000 : ℝ), (10784205266891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071074577/2000000000 : ℝ)|^4707 ≤ (22508884990091/50000000000000 : ℝ)^3683
        have hw : |(1071074577/2000000000 : ℝ)|=(1071074577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884072879/10000000000 : ℝ)|^4707 ≤ (11845408932729/100000000000000 : ℝ)^3683
        have hw : |(-1884072879/10000000000 : ℝ)|=(1884072879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179481853/10000000000 : ℝ)|^4707 ≤ (10784205266891/25000000000000 : ℝ)^3683
        have hw : |(5179481853/10000000000 : ℝ)|=(5179481853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355372941/10000000000 : ℝ)*x 0 + (1294870451/2500000000 : ℝ)*x 1 + (-188407287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355372941/10000000000 : ℝ)^4707 ≤ (9003554116361/20000000000000 : ℝ)^3683 := by
    have hnat : (5355372941 : ℕ)^4707*20000000000000^3683 ≤ 9003554116361^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355372941 10000000000 9003554116361 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294870451/2500000000 : ℝ)^4707 ≤ (43136820546009/100000000000000 : ℝ)^3683 := by
    have hnat : (1294870451 : ℕ)^4707*100000000000000^3683 ≤ 43136820546009^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294870451 2500000000 43136820546009 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188407287/1000000000 : ℝ)^4707 ≤ (11845408860413/100000000000000 : ℝ)^3683 := by
    have hnat : (188407287 : ℕ)^4707*100000000000000^3683 ≤ 11845408860413^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188407287 1000000000 11845408860413 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355372941/10000000000 : ℝ), (1294870451/2500000000 : ℝ), (-188407287/1000000000 : ℝ)] ![(9003554116361/20000000000000 : ℝ), (43136820546009/100000000000000 : ℝ), (11845408860413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355372941/10000000000 : ℝ)|^4707 ≤ (9003554116361/20000000000000 : ℝ)^3683
        have hw : |(5355372941/10000000000 : ℝ)|=(5355372941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294870451/2500000000 : ℝ)|^4707 ≤ (43136820546009/100000000000000 : ℝ)^3683
        have hw : |(1294870451/2500000000 : ℝ)|=(1294870451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188407287/1000000000 : ℝ)|^4707 ≤ (11845408860413/100000000000000 : ℝ)^3683
        have hw : |(-188407287/1000000000 : ℝ)|=(188407287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2111698571/5000000000 : ℝ)*x 0 + (3891408519/10000000000 : ℝ)*x 1 + (4577264957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111698571/5000000000 : ℝ)^4707 ≤ (3323403932029/10000000000000 : ℝ)^3683 := by
    have hnat : (2111698571 : ℕ)^4707*10000000000000^3683 ≤ 3323403932029^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111698571 5000000000 3323403932029 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3891408519/10000000000 : ℝ)^4707 ≤ (29932466133053/100000000000000 : ℝ)^3683 := by
    have hnat : (3891408519 : ℕ)^4707*100000000000000^3683 ≤ 29932466133053^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3891408519 10000000000 29932466133053 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577264957/10000000000 : ℝ)^4707 ≤ (36833494534199/100000000000000 : ℝ)^3683 := by
    have hnat : (4577264957 : ℕ)^4707*100000000000000^3683 ≤ 36833494534199^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577264957 10000000000 36833494534199 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2111698571/5000000000 : ℝ), (3891408519/10000000000 : ℝ), (4577264957/10000000000 : ℝ)] ![(3323403932029/10000000000000 : ℝ), (29932466133053/100000000000000 : ℝ), (36833494534199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2111698571/5000000000 : ℝ)|^4707 ≤ (3323403932029/10000000000000 : ℝ)^3683
        have hw : |(2111698571/5000000000 : ℝ)|=(2111698571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3891408519/10000000000 : ℝ)|^4707 ≤ (29932466133053/100000000000000 : ℝ)^3683
        have hw : |(3891408519/10000000000 : ℝ)|=(3891408519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577264957/10000000000 : ℝ)|^4707 ≤ (36833494534199/100000000000000 : ℝ)^3683
        have hw : |(4577264957/10000000000 : ℝ)|=(4577264957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868818153/5000000000 : ℝ)*x 0 + (103631593/200000000 : ℝ)*x 1 + (1365330409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868818153/5000000000 : ℝ)^4707 ≤ (10681726389139/100000000000000 : ℝ)^3683 := by
    have hnat : (868818153 : ℕ)^4707*100000000000000^3683 ≤ 10681726389139^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868818153 5000000000 10681726389139 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103631593/200000000 : ℝ)^4707 ≤ (43159151246873/100000000000000 : ℝ)^3683 := by
    have hnat : (103631593 : ℕ)^4707*100000000000000^3683 ≤ 43159151246873^3683*200000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103631593 200000000 43159151246873 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365330409/2500000000 : ℝ)^4707 ≤ (9231824469941/20000000000000 : ℝ)^3683 := by
    have hnat : (1365330409 : ℕ)^4707*20000000000000^3683 ≤ 9231824469941^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365330409 2500000000 9231824469941 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868818153/5000000000 : ℝ), (103631593/200000000 : ℝ), (1365330409/2500000000 : ℝ)] ![(10681726389139/100000000000000 : ℝ), (43159151246873/100000000000000 : ℝ), (9231824469941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868818153/5000000000 : ℝ)|^4707 ≤ (10681726389139/100000000000000 : ℝ)^3683
        have hw : |(-868818153/5000000000 : ℝ)|=(868818153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103631593/200000000 : ℝ)|^4707 ≤ (43159151246873/100000000000000 : ℝ)^3683
        have hw : |(103631593/200000000 : ℝ)|=(103631593/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365330409/2500000000 : ℝ)|^4707 ≤ (9231824469941/20000000000000 : ℝ)^3683
        have hw : |(1365330409/2500000000 : ℝ)|=(1365330409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640073887/5000000000 : ℝ)*x 0 + (-1602233059/10000000000 : ℝ)*x 1 + (5461321653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640073887/5000000000 : ℝ)^4707 ≤ (44211189324797/100000000000000 : ℝ)^3683 := by
    have hnat : (2640073887 : ℕ)^4707*100000000000000^3683 ≤ 44211189324797^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640073887 5000000000 44211189324797 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1602233059/10000000000 : ℝ)^4707 ≤ (1203711016801/12500000000000 : ℝ)^3683 := by
    have hnat : (1602233059 : ℕ)^4707*12500000000000^3683 ≤ 1203711016801^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602233059 10000000000 1203711016801 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461321653/10000000000 : ℝ)^4707 ≤ (23079561266669/50000000000000 : ℝ)^3683 := by
    have hnat : (5461321653 : ℕ)^4707*50000000000000^3683 ≤ 23079561266669^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461321653 10000000000 23079561266669 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640073887/5000000000 : ℝ), (-1602233059/10000000000 : ℝ), (5461321653/10000000000 : ℝ)] ![(44211189324797/100000000000000 : ℝ), (1203711016801/12500000000000 : ℝ), (23079561266669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640073887/5000000000 : ℝ)|^4707 ≤ (44211189324797/100000000000000 : ℝ)^3683
        have hw : |(2640073887/5000000000 : ℝ)|=(2640073887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1602233059/10000000000 : ℝ)|^4707 ≤ (1203711016801/12500000000000 : ℝ)^3683
        have hw : |(-1602233059/10000000000 : ℝ)|=(1602233059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461321653/10000000000 : ℝ)|^4707 ≤ (23079561266669/50000000000000 : ℝ)^3683
        have hw : |(5461321653/10000000000 : ℝ)|=(5461321653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280147787/10000000000 : ℝ)*x 0 + (341332603/625000000 : ℝ)*x 1 + (-1602233047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280147787/10000000000 : ℝ)^4707 ≤ (5526398682989/12500000000000 : ℝ)^3683 := by
    have hnat : (5280147787 : ℕ)^4707*12500000000000^3683 ≤ 5526398682989^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280147787 10000000000 5526398682989 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341332603/625000000 : ℝ)^4707 ≤ (1442472577479/3125000000000 : ℝ)^3683 := by
    have hnat : (341332603 : ℕ)^4707*3125000000000^3683 ≤ 1442472577479^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341332603 625000000 1442472577479 3125000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602233047/10000000000 : ℝ)^4707 ≤ (9629688042233/100000000000000 : ℝ)^3683 := by
    have hnat : (1602233047 : ℕ)^4707*100000000000000^3683 ≤ 9629688042233^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602233047 10000000000 9629688042233 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280147787/10000000000 : ℝ), (341332603/625000000 : ℝ), (-1602233047/10000000000 : ℝ)] ![(5526398682989/12500000000000 : ℝ), (1442472577479/3125000000000 : ℝ), (9629688042233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280147787/10000000000 : ℝ)|^4707 ≤ (5526398682989/12500000000000 : ℝ)^3683
        have hw : |(5280147787/10000000000 : ℝ)|=(5280147787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341332603/625000000 : ℝ)|^4707 ≤ (1442472577479/3125000000000 : ℝ)^3683
        have hw : |(341332603/625000000 : ℝ)|=(341332603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1602233047/10000000000 : ℝ)|^4707 ≤ (9629688042233/100000000000000 : ℝ)^3683
        have hw : |(-1602233047/10000000000 : ℝ)|=(1602233047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s5_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223572159/10000000000 : ℝ)*x 0 + (4572197991/10000000000 : ℝ)*x 1 + (1948264307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223572159/10000000000 : ℝ)^4707 ≤ (6647159891419/20000000000000 : ℝ)^3683 := by
    have hnat : (4223572159 : ℕ)^4707*20000000000000^3683 ≤ 6647159891419^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223572159 10000000000 6647159891419 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572197991/10000000000 : ℝ)^4707 ≤ (36781391803577/100000000000000 : ℝ)^3683 := by
    have hnat : (4572197991 : ℕ)^4707*100000000000000^3683 ≤ 36781391803577^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572197991 10000000000 36781391803577 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948264307/5000000000 : ℝ)^4707 ≤ (29982808725679/100000000000000 : ℝ)^3683 := by
    have hnat : (1948264307 : ℕ)^4707*100000000000000^3683 ≤ 29982808725679^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948264307 5000000000 29982808725679 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223572159/10000000000 : ℝ), (4572197991/10000000000 : ℝ), (1948264307/5000000000 : ℝ)] ![(6647159891419/20000000000000 : ℝ), (36781391803577/100000000000000 : ℝ), (29982808725679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223572159/10000000000 : ℝ)|^4707 ≤ (6647159891419/20000000000000 : ℝ)^3683
        have hw : |(4223572159/10000000000 : ℝ)|=(4223572159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572197991/10000000000 : ℝ)|^4707 ≤ (36781391803577/100000000000000 : ℝ)^3683
        have hw : |(4572197991/10000000000 : ℝ)|=(4572197991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1948264307/5000000000 : ℝ)|^4707 ≤ (29982808725679/100000000000000 : ℝ)^3683
        have hw : |(1948264307/5000000000 : ℝ)|=(1948264307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8181/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2069/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2069/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2069/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2069/20000 : ℝ) ^ (4703/1024 : ℝ) ≤ (596912102430949/20000000000000000000 : ℝ) := by
    have hpowers : (2069/20000 : ℝ)^4703 ≤ (596912102430949/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2069 : ℕ)^4703*20000000000000000000^1024 ≤ 596912102430949^1024*20000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2069 20000 596912102430949 20000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2069/20000 : ℝ)) (X := (596912102430949/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4703/1024 : ℝ) ≤ (12261467377653437/50000000000000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4703 ≤ (12261467377653437/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4703*50000000000000000000^1024 ≤ 12261467377653437^1024*25000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 12261467377653437 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (12261467377653437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000596912102430949/10000000000000000000 : ℝ) ≤ (156252030697569/156250000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (10000596912102430949/10000000000000000000 : ℝ)^1024 ≤ (156252030697569/156250000000000 : ℝ)^4703 := by
      have hnat : (10000596912102430949 : ℕ)^1024*156250000000000^4703 ≤ 156252030697569^4703*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000596912102430949 10000000000000000000 156252030697569 156250000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156252030697569/156250000000000 : ℝ)) (X := (10000596912102430949/10000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027507495267461619/100000000000000000000 : ℝ) ≤ (10000598865512679/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (100027507495267461619/100000000000000000000 : ℝ)^1024 ≤ (10000598865512679/10000000000000000 : ℝ)^4703 := by
      have hnat : (100027507495267461619 : ℕ)^1024*10000000000000000^4703 ≤ 10000598865512679^4703*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027507495267461619 100000000000000000000 10000598865512679 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000598865512679/10000000000000000 : ℝ)) (X := (100027507495267461619/100000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012261467377653437/25000000000000000000 : ℝ) ≤ (5000533883190471/5000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25012261467377653437/25000000000000000000 : ℝ)^1024 ≤ (5000533883190471/5000000000000000 : ℝ)^4703 := by
      have hnat : (25012261467377653437 : ℕ)^1024*5000000000000000^4703 ≤ 5000533883190471^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012261467377653437 25000000000000000000 5000533883190471 5000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000533883190471/5000000000000000 : ℝ)) (X := (25012261467377653437/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(596912102430949/20000000000000000000 : ℝ) ≤ ((30090540349115189217/30095000000000000000 : ℝ)+2*(468900868263/601900000000000 : ℝ)*(2069/20000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (30090540349115189217/30095000000000000000 : ℝ)+2*(468900868263/601900000000000 : ℝ)*(2069/20000 : ℝ)=(156252030697569/156250000000000 : ℝ) by norm_num, show 1+2*(596912102430949/20000000000000000000 : ℝ)=(10000596912102430949/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12261467377653437/50000000000000000000 : ℝ)+(596912102430949/20000000000000000000 : ℝ) ≤ ((30090540349115189217/30095000000000000000 : ℝ)+(468900868263/601900000000000 : ℝ)*((4091/25000 : ℝ)+(2069/20000 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (30090540349115189217/30095000000000000000 : ℝ)+(468900868263/601900000000000 : ℝ)*((4091/25000 : ℝ)+(2069/20000 : ℝ))=(10000598865512679/10000000000000000 : ℝ) by norm_num, show 1+(12261467377653437/50000000000000000000 : ℝ)+(596912102430949/20000000000000000000 : ℝ)=(100027507495267461619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12261467377653437/50000000000000000000 : ℝ) ≤ ((30090540349115189217/30095000000000000000 : ℝ)+2*(468900868263/601900000000000 : ℝ)*(4091/25000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (30090540349115189217/30095000000000000000 : ℝ)+2*(468900868263/601900000000000 : ℝ)*(4091/25000 : ℝ)=(5000533883190471/5000000000000000 : ℝ) by norm_num, show 1+2*(12261467377653437/50000000000000000000 : ℝ)=(25012261467377653437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30090540349115189217/30095000000000000000 : ℝ)*(X 1 0+X 2 0)+(468900868263/601900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (30090540349115189217/30095000000000000000 : ℝ)) (alpha := (468900868263/601900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30090540349115189217/30095000000000000000 : ℝ)*(X 0 1+X 2 1)+(468900868263/601900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (30090540349115189217/30095000000000000000 : ℝ)) (alpha := (468900868263/601900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30090540349115189217/30095000000000000000 : ℝ)*(X 0 2+X 1 2)+(468900868263/601900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (2069/20000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (30090540349115189217/30095000000000000000 : ℝ)) (alpha := (468900868263/601900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1737563879/10000000000 : ℝ)*X 0 0+(170732549/312500000 : ℝ)*X 0 1+(5179481717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071074577/2000000000 : ℝ)*X 1 0+(-1884072879/10000000000 : ℝ)*X 1 1+(5179481853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355372941/10000000000 : ℝ)*X 2 0+(1294870451/2500000000 : ℝ)*X 2 1+(-188407287/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2111698571/5000000000 : ℝ)*X 0 0+(3891408519/10000000000 : ℝ)*X 0 1+(4577264957/10000000000 : ℝ)*X 0 2+(2111698571/5000000000 : ℝ)*X 1 0+(3891408519/10000000000 : ℝ)*X 1 1+(4577264957/10000000000 : ℝ)*X 1 2+(2111698571/5000000000 : ℝ)*X 2 0+(3891408519/10000000000 : ℝ)*X 2 1+(4577264957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-868818153/5000000000 : ℝ)*X 0 0+(103631593/200000000 : ℝ)*X 0 1+(1365330409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640073887/5000000000 : ℝ)*X 1 0+(-1602233059/10000000000 : ℝ)*X 1 1+(5461321653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280147787/10000000000 : ℝ)*X 2 0+(341332603/625000000 : ℝ)*X 2 1+(-1602233047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4223572159/10000000000 : ℝ)*X 0 0+(4572197991/10000000000 : ℝ)*X 0 1+(1948264307/5000000000 : ℝ)*X 0 2+(4223572159/10000000000 : ℝ)*X 1 0+(4572197991/10000000000 : ℝ)*X 1 1+(1948264307/5000000000 : ℝ)*X 1 2+(4223572159/10000000000 : ℝ)*X 2 0+(4572197991/10000000000 : ℝ)*X 2 1+(1948264307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50194850046331004759106351/18809375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (437351663/100000000000000 : ℝ)*(base19) + (473153123/100000000000000 : ℝ)*(base23) + (51866761/100000000000000 : ℝ)*(upper3) + (274079/50000000000000 : ℝ)*(upper4) + (63831181/100000000000000 : ℝ)*(upper5) + (31122968710049/1250000000000 : ℝ)*(major0) + (31122968710049/1250000000000 : ℝ)*(major1) + (31122968710049/1250000000000 : ℝ)*(major2) + (1760815710380861/50000000000000 : ℝ)*(sp0) + (176081916140677/5000000000000 : ℝ)*(sp1) + (44020478587651/1250000000000 : ℝ)*(sp2) + (1458033606132747/100000000000000 : ℝ)*(sp3) + (7339403481/100000000000000 : ℝ)*(sp4) + (2538356283/100000000000000 : ℝ)*(sp7) + (145803614448903/10000000000000 : ℝ)*(f.failure) + (3521638760165203/100000000000000 : ℝ)*(f.sum) + (4029364835501/6019000000000000000000000000 : ℝ)*base66 + (89945179232766633/37618750000000000000000000000000 : ℝ)*base67 + (135864155098760383/37618750000000000000000000000000 : ℝ)*base69 + (82463709735885383/37618750000000000000000000000000 : ℝ)*base71 + (2420977675021/3009500000000000000000000000 : ℝ)*base74 + (123751793042302117/37618750000000000000000000000000 : ℝ)*base76 + (234997795340760383/37618750000000000000000000000000 : ℝ)*base77 + (188485130047895867/37618750000000000000000000000000 : ℝ)*base80 + (13987634130413/6019000000000000000000000000 : ℝ)*base81 + (1782929/500000000000000000000 : ℝ)*base90 + (1782929/500000000000000000000 : ℝ)*base92 + (1782929/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1069671724699676276954259567/376187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1435337/312500000000 : ℝ)*(base19) + (500863909/100000000000000 : ℝ)*(base23) + (147105427/100000000000000 : ℝ)*(lower1) + (13487329/20000000000000 : ℝ)*(upper3) + (12350277/100000000000000 : ℝ)*(lower4) + (55110937/100000000000000 : ℝ)*(upper5) + (631841092377983/25000000000000 : ℝ)*(major0) + (631841092377983/25000000000000 : ℝ)*(major1) + (631841092377983/25000000000000 : ℝ)*(major2) + (657334521/100000000000000 : ℝ)*(sp2) + (1787358477206987/50000000000000 : ℝ)*(sp4) + (1787358247553067/50000000000000 : ℝ)*(sp5) + (446839474526943/12500000000000 : ℝ)*(sp6) + (5781295663391/390625000000 : ℝ)*(sp7) + (5781295663391/390625000000 : ℝ)*(f.failure) + (1787358477206987/50000000000000 : ℝ)*(f.sum) + (15872931838973/3761875000000000000000000000 : ℝ)*base66 + (3413287929645759311/752375000000000000000000000000000 : ℝ)*base67 + (3549320209737259311/752375000000000000000000000000000 : ℝ)*base69 + (7258655437621240689/752375000000000000000000000000000 : ℝ)*base72 + (19681342473633/15047500000000000000000000000 : ℝ)*base73 + (8669534216602990689/752375000000000000000000000000000 : ℝ)*base76 + (835882597405384311/752375000000000000000000000000000 : ℝ)*base77 + (9260879377317759311/752375000000000000000000000000000 : ℝ)*base79 + (26734776060477/15047500000000000000000000000 : ℝ)*base82 + (25737/19531250000000000000 : ℝ)*base89 + (25737/19531250000000000000 : ℝ)*base91 + (25737/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1597_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2069/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1597_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1597_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1597_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1597_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
