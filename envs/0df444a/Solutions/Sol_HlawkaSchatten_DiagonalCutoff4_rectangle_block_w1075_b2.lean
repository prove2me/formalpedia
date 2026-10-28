-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:13:25.269577+00:00
-- url     : https://prove2.me/submissions/b58819b3-e661-467c-91a8-e5e0656d6839

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
theorem support_rectangle_w1075_s6_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199296757/10000000000 : ℝ)*x 0 + (5394733467/10000000000 : ℝ)*x 1 + (5264114637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199296757/10000000000 : ℝ)^2067 ≤ (6678730469881/50000000000000 : ℝ)^1555 := by
    have hnat : (2199296757 : ℕ)^2067*50000000000000^1555 ≤ 6678730469881^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199296757 10000000000 6678730469881 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394733467/10000000000 : ℝ)^2067 ≤ (44026920748657/100000000000000 : ℝ)^1555 := by
    have hnat : (5394733467 : ℕ)^2067*100000000000000^1555 ≤ 44026920748657^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394733467 10000000000 44026920748657 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264114637/10000000000 : ℝ)^2067 ≤ (21307809146731/50000000000000 : ℝ)^1555 := by
    have hnat : (5264114637 : ℕ)^2067*50000000000000^1555 ≤ 21307809146731^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264114637 10000000000 21307809146731 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199296757/10000000000 : ℝ), (5394733467/10000000000 : ℝ), (5264114637/10000000000 : ℝ)] ![(6678730469881/50000000000000 : ℝ), (44026920748657/100000000000000 : ℝ), (21307809146731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199296757/10000000000 : ℝ)|^2067 ≤ (6678730469881/50000000000000 : ℝ)^1555
        have hw : |(-2199296757/10000000000 : ℝ)|=(2199296757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394733467/10000000000 : ℝ)|^2067 ≤ (44026920748657/100000000000000 : ℝ)^1555
        have hw : |(5394733467/10000000000 : ℝ)|=(5394733467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264114637/10000000000 : ℝ)|^2067 ≤ (21307809146731/50000000000000 : ℝ)^1555
        have hw : |(5264114637/10000000000 : ℝ)|=(5264114637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345091479/10000000000 : ℝ)*x 0 + (-226557359/1000000000 : ℝ)*x 1 + (1052822947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345091479/10000000000 : ℝ)^2067 ≤ (43489211151419/100000000000000 : ℝ)^1555 := by
    have hnat : (5345091479 : ℕ)^2067*100000000000000^1555 ≤ 43489211151419^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345091479 10000000000 43489211151419 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226557359/1000000000 : ℝ)^2067 ≤ (694758474453/5000000000000 : ℝ)^1555 := by
    have hnat : (226557359 : ℕ)^2067*5000000000000^1555 ≤ 694758474453^1555*1000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226557359 1000000000 694758474453 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052822947/2000000000 : ℝ)^2067 ≤ (21307809674021/50000000000000 : ℝ)^1555 := by
    have hnat : (1052822947 : ℕ)^2067*50000000000000^1555 ≤ 21307809674021^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052822947 2000000000 21307809674021 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345091479/10000000000 : ℝ), (-226557359/1000000000 : ℝ), (1052822947/2000000000 : ℝ)] ![(43489211151419/100000000000000 : ℝ), (694758474453/5000000000000 : ℝ), (21307809674021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345091479/10000000000 : ℝ)|^2067 ≤ (43489211151419/100000000000000 : ℝ)^1555
        have hw : |(5345091479/10000000000 : ℝ)|=(5345091479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226557359/1000000000 : ℝ)|^2067 ≤ (694758474453/5000000000000 : ℝ)^1555
        have hw : |(-226557359/1000000000 : ℝ)|=(226557359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052822947/2000000000 : ℝ)|^2067 ≤ (21307809674021/50000000000000 : ℝ)^1555
        have hw : |(1052822947/2000000000 : ℝ)|=(1052822947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334068201/625000000 : ℝ)*x 0 + (5264114871/10000000000 : ℝ)*x 1 + (-2265573759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334068201/625000000 : ℝ)^2067 ≤ (679518879797/1562500000000 : ℝ)^1555 := by
    have hnat : (334068201 : ℕ)^2067*1562500000000^1555 ≤ 679518879797^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334068201 625000000 679518879797 1562500000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264114871/10000000000 : ℝ)^2067 ≤ (42615620811541/100000000000000 : ℝ)^1555 := by
    have hnat : (5264114871 : ℕ)^2067*100000000000000^1555 ≤ 42615620811541^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264114871 10000000000 42615620811541 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265573759/10000000000 : ℝ)^2067 ≤ (434224089589/3125000000000 : ℝ)^1555 := by
    have hnat : (2265573759 : ℕ)^2067*3125000000000^1555 ≤ 434224089589^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265573759 10000000000 434224089589 3125000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334068201/625000000 : ℝ), (5264114871/10000000000 : ℝ), (-2265573759/10000000000 : ℝ)] ![(679518879797/1562500000000 : ℝ), (42615620811541/100000000000000 : ℝ), (434224089589/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334068201/625000000 : ℝ)|^2067 ≤ (679518879797/1562500000000 : ℝ)^1555
        have hw : |(334068201/625000000 : ℝ)|=(334068201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264114871/10000000000 : ℝ)|^2067 ≤ (42615620811541/100000000000000 : ℝ)^1555
        have hw : |(5264114871/10000000000 : ℝ)|=(5264114871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2265573759/10000000000 : ℝ)|^2067 ≤ (434224089589/3125000000000 : ℝ)^1555
        have hw : |(-2265573759/10000000000 : ℝ)|=(2265573759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4374172971/10000000000 : ℝ)*x 0 + (4247846777/10000000000 : ℝ)*x 1 + (4504298961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374172971/10000000000 : ℝ)^2067 ≤ (4164541606967/12500000000000 : ℝ)^1555 := by
    have hnat : (4374172971 : ℕ)^2067*12500000000000^1555 ≤ 4164541606967^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374172971 10000000000 4164541606967 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247846777/10000000000 : ℝ)^2067 ≤ (6408694133149/20000000000000 : ℝ)^1555 := by
    have hnat : (4247846777 : ℕ)^2067*20000000000000^1555 ≤ 6408694133149^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247846777 10000000000 6408694133149 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504298961/10000000000 : ℝ)^2067 ≤ (34640196467327/100000000000000 : ℝ)^1555 := by
    have hnat : (4504298961 : ℕ)^2067*100000000000000^1555 ≤ 34640196467327^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504298961 10000000000 34640196467327 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374172971/10000000000 : ℝ), (4247846777/10000000000 : ℝ), (4504298961/10000000000 : ℝ)] ![(4164541606967/12500000000000 : ℝ), (6408694133149/20000000000000 : ℝ), (34640196467327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374172971/10000000000 : ℝ)|^2067 ≤ (4164541606967/12500000000000 : ℝ)^1555
        have hw : |(4374172971/10000000000 : ℝ)|=(4374172971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247846777/10000000000 : ℝ)|^2067 ≤ (6408694133149/20000000000000 : ℝ)^1555
        have hw : |(4247846777/10000000000 : ℝ)|=(4247846777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504298961/10000000000 : ℝ)|^2067 ≤ (34640196467327/100000000000000 : ℝ)^1555
        have hw : |(4504298961/10000000000 : ℝ)|=(4504298961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099650967/5000000000 : ℝ)*x 0 + (2632222299/5000000000 : ℝ)*x 1 + (5394402299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099650967/5000000000 : ℝ)^2067 ≤ (13357502735163/100000000000000 : ℝ)^1555 := by
    have hnat : (1099650967 : ℕ)^2067*100000000000000^1555 ≤ 13357502735163^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099650967 5000000000 13357502735163 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632222299/5000000000 : ℝ)^2067 ≤ (42619169047841/100000000000000 : ℝ)^1555 := by
    have hnat : (2632222299 : ℕ)^2067*100000000000000^1555 ≤ 42619169047841^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632222299 5000000000 42619169047841 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394402299/10000000000 : ℝ)^2067 ≤ (44023328202319/100000000000000 : ℝ)^1555 := by
    have hnat : (5394402299 : ℕ)^2067*100000000000000^1555 ≤ 44023328202319^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394402299 10000000000 44023328202319 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099650967/5000000000 : ℝ), (2632222299/5000000000 : ℝ), (5394402299/10000000000 : ℝ)] ![(13357502735163/100000000000000 : ℝ), (42619169047841/100000000000000 : ℝ), (44023328202319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099650967/5000000000 : ℝ)|^2067 ≤ (13357502735163/100000000000000 : ℝ)^1555
        have hw : |(-1099650967/5000000000 : ℝ)|=(1099650967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632222299/5000000000 : ℝ)|^2067 ≤ (42619169047841/100000000000000 : ℝ)^1555
        have hw : |(2632222299/5000000000 : ℝ)|=(2632222299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394402299/10000000000 : ℝ)|^2067 ≤ (44023328202319/100000000000000 : ℝ)^1555
        have hw : |(5394402299/10000000000 : ℝ)|=(5394402299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328041941/2500000000 : ℝ)*x 0 + (-21352861/100000000 : ℝ)*x 1 + (5394402289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328041941/2500000000 : ℝ)^2067 ≤ (43133494600897/100000000000000 : ℝ)^1555 := by
    have hnat : (1328041941 : ℕ)^2067*100000000000000^1555 ≤ 43133494600897^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328041941 2500000000 43133494600897 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21352861/100000000 : ℝ)^2067 ≤ (3210794322467/25000000000000 : ℝ)^1555 := by
    have hnat : (21352861 : ℕ)^2067*25000000000000^1555 ≤ 3210794322467^1555*100000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21352861 100000000 3210794322467 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394402289/10000000000 : ℝ)^2067 ≤ (44023328093839/100000000000000 : ℝ)^1555 := by
    have hnat : (5394402289 : ℕ)^2067*100000000000000^1555 ≤ 44023328093839^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394402289 10000000000 44023328093839 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328041941/2500000000 : ℝ), (-21352861/100000000 : ℝ), (5394402289/10000000000 : ℝ)] ![(43133494600897/100000000000000 : ℝ), (3210794322467/25000000000000 : ℝ), (44023328093839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328041941/2500000000 : ℝ)|^2067 ≤ (43133494600897/100000000000000 : ℝ)^1555
        have hw : |(1328041941/2500000000 : ℝ)|=(1328041941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21352861/100000000 : ℝ)|^2067 ≤ (3210794322467/25000000000000 : ℝ)^1555
        have hw : |(-21352861/100000000 : ℝ)|=(21352861/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394402289/10000000000 : ℝ)|^2067 ≤ (44023328093839/100000000000000 : ℝ)^1555
        have hw : |(5394402289/10000000000 : ℝ)|=(5394402289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312167509/10000000000 : ℝ)*x 0 + (5394402643/10000000000 : ℝ)*x 1 + (-533821491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312167509/10000000000 : ℝ)^2067 ≤ (21566745924307/50000000000000 : ℝ)^1555 := by
    have hnat : (5312167509 : ℕ)^2067*50000000000000^1555 ≤ 21566745924307^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312167509 10000000000 21566745924307 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394402643/10000000000 : ℝ)^2067 ≤ (4402333193403/10000000000000 : ℝ)^1555 := by
    have hnat : (5394402643 : ℕ)^2067*10000000000000^1555 ≤ 4402333193403^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394402643 10000000000 4402333193403 10000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533821491/2500000000 : ℝ)^2067 ≤ (401349256329/3125000000000 : ℝ)^1555 := by
    have hnat : (533821491 : ℕ)^2067*3125000000000^1555 ≤ 401349256329^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533821491 2500000000 401349256329 3125000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312167509/10000000000 : ℝ), (5394402643/10000000000 : ℝ), (-533821491/2500000000 : ℝ)] ![(21566745924307/50000000000000 : ℝ), (4402333193403/10000000000000 : ℝ), (401349256329/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312167509/10000000000 : ℝ)|^2067 ≤ (21566745924307/50000000000000 : ℝ)^1555
        have hw : |(5312167509/10000000000 : ℝ)|=(5312167509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394402643/10000000000 : ℝ)|^2067 ≤ (4402333193403/10000000000000 : ℝ)^1555
        have hw : |(5394402643/10000000000 : ℝ)|=(5394402643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533821491/2500000000 : ℝ)|^2067 ≤ (401349256329/3125000000000 : ℝ)^1555
        have hw : |(-533821491/2500000000 : ℝ)|=(533821491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s6_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2187091543/5000000000 : ℝ)*x 0 + (900730239/2000000000 : ℝ)*x 1 + (2124248461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187091543/5000000000 : ℝ)^2067 ≤ (33316435264559/100000000000000 : ℝ)^1555 := by
    have hnat : (2187091543 : ℕ)^2067*100000000000000^1555 ≤ 33316435264559^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187091543 5000000000 33316435264559 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900730239/2000000000 : ℝ)^2067 ≤ (17316787371563/50000000000000 : ℝ)^1555 := by
    have hnat : (900730239 : ℕ)^2067*50000000000000^1555 ≤ 17316787371563^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900730239 2000000000 17316787371563 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124248461/5000000000 : ℝ)^2067 ≤ (8012497495159/25000000000000 : ℝ)^1555 := by
    have hnat : (2124248461 : ℕ)^2067*25000000000000^1555 ≤ 8012497495159^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124248461 5000000000 8012497495159 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187091543/5000000000 : ℝ), (900730239/2000000000 : ℝ), (2124248461/5000000000 : ℝ)] ![(33316435264559/100000000000000 : ℝ), (17316787371563/50000000000000 : ℝ), (8012497495159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187091543/5000000000 : ℝ)|^2067 ≤ (33316435264559/100000000000000 : ℝ)^1555
        have hw : |(2187091543/5000000000 : ℝ)|=(2187091543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900730239/2000000000 : ℝ)|^2067 ≤ (17316787371563/50000000000000 : ℝ)^1555
        have hw : |(900730239/2000000000 : ℝ)|=(900730239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124248461/5000000000 : ℝ)|^2067 ≤ (8012497495159/25000000000000 : ℝ)^1555
        have hw : |(2124248461/5000000000 : ℝ)|=(2124248461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11213/100000 : ℝ) ^ (8267/2048 : ℝ) ≤ (2918213471840053/20000000000000000000 : ℝ) := by
    have hpowers : (11213/100000 : ℝ)^8267 ≤ (2918213471840053/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11213 : ℕ)^8267*20000000000000000000^2048 ≤ 2918213471840053^2048*100000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11213 100000 2918213471840053 20000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11213/100000 : ℝ)) (X := (2918213471840053/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (8267/2048 : ℝ) ≤ (18195287889765139/50000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^8267 ≤ (18195287889765139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7031 : ℕ)^8267*50000000000000000000^2048 ≤ 18195287889765139^2048*50000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 18195287889765139 50000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (18195287889765139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002918213471840053/10000000000000000000 : ℝ) ≤ (10000722855364439/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (10002918213471840053/10000000000000000000 : ℝ)^2048 ≤ (10000722855364439/10000000000000000 : ℝ)^8267 := by
      have hnat : (10002918213471840053 : ℕ)^2048*10000000000000000^8267 ≤ 10000722855364439^8267*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002918213471840053 10000000000000000000 10000722855364439 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722855364439/10000000000000000 : ℝ)) (X := (10002918213471840053/10000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050981643138730543/100000000000000000000 : ℝ) ≤ (1000126273605227/1000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (100050981643138730543/100000000000000000000 : ℝ)^2048 ≤ (1000126273605227/1000000000000000 : ℝ)^8267 := by
      have hnat : (100050981643138730543 : ℕ)^2048*1000000000000000^8267 ≤ 1000126273605227^8267*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050981643138730543 100000000000000000000 1000126273605227 1000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000126273605227/1000000000000000 : ℝ)) (X := (100050981643138730543/100000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018195287889765139/25000000000000000000 : ℝ) ≤ (10001802616740101/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (25018195287889765139/25000000000000000000 : ℝ)^2048 ≤ (10001802616740101/10000000000000000 : ℝ)^8267 := by
      have hnat : (25018195287889765139 : ℕ)^2048*10000000000000000^8267 ≤ 10001802616740101^8267*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018195287889765139 25000000000000000000 10001802616740101 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001802616740101/10000000000000000 : ℝ)) (X := (25018195287889765139/25000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2918213471840053/20000000000000000000 : ℝ) ≤ ((5695990410125597741/5698000000000000000 : ℝ)+2*(539880687831/284900000000000 : ℝ)*(11213/100000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (5695990410125597741/5698000000000000000 : ℝ)+2*(539880687831/284900000000000 : ℝ)*(11213/100000 : ℝ)=(10000722855364439/10000000000000000 : ℝ) by norm_num, show 1+2*(2918213471840053/20000000000000000000 : ℝ)=(10002918213471840053/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18195287889765139/50000000000000000000 : ℝ)+(2918213471840053/20000000000000000000 : ℝ) ≤ ((5695990410125597741/5698000000000000000 : ℝ)+(539880687831/284900000000000 : ℝ)*((7031/50000 : ℝ)+(11213/100000 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (5695990410125597741/5698000000000000000 : ℝ)+(539880687831/284900000000000 : ℝ)*((7031/50000 : ℝ)+(11213/100000 : ℝ))=(1000126273605227/1000000000000000 : ℝ) by norm_num, show 1+(18195287889765139/50000000000000000000 : ℝ)+(2918213471840053/20000000000000000000 : ℝ)=(100050981643138730543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18195287889765139/50000000000000000000 : ℝ) ≤ ((5695990410125597741/5698000000000000000 : ℝ)+2*(539880687831/284900000000000 : ℝ)*(7031/50000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (5695990410125597741/5698000000000000000 : ℝ)+2*(539880687831/284900000000000 : ℝ)*(7031/50000 : ℝ)=(10001802616740101/10000000000000000 : ℝ) by norm_num, show 1+2*(18195287889765139/50000000000000000000 : ℝ)=(25018195287889765139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5695990410125597741/5698000000000000000 : ℝ)*(X 1 0+X 2 0)+(539880687831/284900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (5695990410125597741/5698000000000000000 : ℝ)) (alpha := (539880687831/284900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5695990410125597741/5698000000000000000 : ℝ)*(X 0 1+X 2 1)+(539880687831/284900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (5695990410125597741/5698000000000000000 : ℝ)) (alpha := (539880687831/284900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5695990410125597741/5698000000000000000 : ℝ)*(X 0 2+X 1 2)+(539880687831/284900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (5695990410125597741/5698000000000000000 : ℝ)) (alpha := (539880687831/284900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2199296757/10000000000 : ℝ)*X 0 0+(5394733467/10000000000 : ℝ)*X 0 1+(5264114637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345091479/10000000000 : ℝ)*X 1 0+(-226557359/1000000000 : ℝ)*X 1 1+(1052822947/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334068201/625000000 : ℝ)*X 2 0+(5264114871/10000000000 : ℝ)*X 2 1+(-2265573759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374172971/10000000000 : ℝ)*X 0 0+(4247846777/10000000000 : ℝ)*X 0 1+(4504298961/10000000000 : ℝ)*X 0 2+(4374172971/10000000000 : ℝ)*X 1 0+(4247846777/10000000000 : ℝ)*X 1 1+(4504298961/10000000000 : ℝ)*X 1 2+(4374172971/10000000000 : ℝ)*X 2 0+(4247846777/10000000000 : ℝ)*X 2 1+(4504298961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1099650967/5000000000 : ℝ)*X 0 0+(2632222299/5000000000 : ℝ)*X 0 1+(5394402299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328041941/2500000000 : ℝ)*X 1 0+(-21352861/100000000 : ℝ)*X 1 1+(5394402289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312167509/10000000000 : ℝ)*X 2 0+(5394402643/10000000000 : ℝ)*X 2 1+(-533821491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187091543/5000000000 : ℝ)*X 0 0+(900730239/2000000000 : ℝ)*X 0 1+(2124248461/5000000000 : ℝ)*X 0 2+(2187091543/5000000000 : ℝ)*X 1 0+(900730239/2000000000 : ℝ)*X 1 1+(2124248461/5000000000 : ℝ)*X 1 2+(2187091543/5000000000 : ℝ)*X 2 0+(900730239/2000000000 : ℝ)*X 2 1+(2124248461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2052577668544446573631444701/284900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737578327/100000000000000 : ℝ)*(base19) + (332024599/25000000000000 : ℝ)*(base23) + (37552801/10000000000000 : ℝ)*(upper3) + (17518929/100000000000000 : ℝ)*(upper4) + (1923539/12500000000000 : ℝ)*(upper5) + (5777689390264187/100000000000000 : ℝ)*(major0) + (5777689390264187/100000000000000 : ℝ)*(major1) + (1444422347566047/25000000000000 : ℝ)*(major2) + (956990575271613/12500000000000 : ℝ)*(sp0) + (1531192592060467/20000000000000 : ℝ)*(sp1) + (3827981684891133/50000000000000 : ℝ)*(sp2) + (389938535172927/10000000000000 : ℝ)*(sp3) + (40095707759/100000000000000 : ℝ)*(sp4) + (7122691651/25000000000000 : ℝ)*(sp7) + (1949706921247937/50000000000000 : ℝ)*(f.failure) + (7655964697880663/100000000000000 : ℝ)*(f.sum) + (57435836699/30800000000000000000000000 : ℝ)*base66 + (2462193986471038433/569800000000000000000000000000000 : ℝ)*base68 + (103607024703334827/142450000000000000000000000000000 : ℝ)*base69 + (10889384708090761567/569800000000000000000000000000000 : ℝ)*base71 + (364800711131/30800000000000000000000000 : ℝ)*base74 + (1405718023804865173/142450000000000000000000000000000 : ℝ)*base76 + (108520500858930629/7400000000000000000000000000000 : ℝ)*base78 + (13609844935330629/7400000000000000000000000000000 : ℝ)*base80 + (5792833248753/1295000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (87854487/5000000000000000000000 : ℝ)*base89 + (87854487/5000000000000000000000 : ℝ)*base91 + (37854487/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1153624751044244533410210681/142450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (443034039/25000000000000 : ℝ)*(base19) + (303430673/20000000000000 : ℝ)*(base23) + (30664093/100000000000000 : ℝ)*(upper2) + (117448201/50000000000000 : ℝ)*(upper3) + (23922763/12500000000000 : ℝ)*(upper5) + (2903500529570447/50000000000000 : ℝ)*(major0) + (2903500529570447/50000000000000 : ℝ)*(major1) + (2903500529570447/50000000000000 : ℝ)*(major2) + (22012210583/50000000000000 : ℝ)*(sp1) + (664593359/1250000000000 : ℝ)*(sp2) + (3847402650195861/50000000000000 : ℝ)*(sp4) + (7694759503834401/100000000000000 : ℝ)*(sp5) + (3847375307884819/50000000000000 : ℝ)*(sp6) + (1959598273970799/50000000000000 : ℝ)*(sp7) + (1959598273970799/50000000000000 : ℝ)*(f.failure) + (3847402650195861/50000000000000 : ℝ)*(f.sum) + (3004782011843/7122500000000000000000000000 : ℝ)*base66 + (302344428268471461/40700000000000000000000000000000 : ℝ)*base67 + (20431108459128539/40700000000000000000000000000000 : ℝ)*base70 + (310067573889528539/40700000000000000000000000000000 : ℝ)*base72 + (402115527967/1780625000000000000000000000 : ℝ)*base74 + (267091668513828539/40700000000000000000000000000000 : ℝ)*base76 + (88609162218328539/40700000000000000000000000000000 : ℝ)*base78 + (427746394929871461/40700000000000000000000000000000 : ℝ)*base79 + (31775841303433/7122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15822649/5000000000000000000000 : ℝ)*base89 + (15822649/5000000000000000000000 : ℝ)*base91 + (15822649/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1075_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1075_s7_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099667931/5000000000 : ℝ)*x 0 + (5394291323/10000000000 : ℝ)*x 1 + (2632265507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099667931/5000000000 : ℝ)^2067 ≤ (1669722080801/12500000000000 : ℝ)^1555 := by
    have hnat : (1099667931 : ℕ)^2067*12500000000000^1555 ≤ 1669722080801^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099667931 5000000000 1669722080801 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394291323/10000000000 : ℝ)^2067 ≤ (22011062169447/50000000000000 : ℝ)^1555 := by
    have hnat : (5394291323 : ℕ)^2067*50000000000000^1555 ≤ 22011062169447^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394291323 10000000000 22011062169447 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632265507/5000000000 : ℝ)^2067 ≤ (8524019798813/20000000000000 : ℝ)^1555 := by
    have hnat : (2632265507 : ℕ)^2067*20000000000000^1555 ≤ 8524019798813^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632265507 5000000000 8524019798813 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099667931/5000000000 : ℝ), (5394291323/10000000000 : ℝ), (2632265507/5000000000 : ℝ)] ![(1669722080801/12500000000000 : ℝ), (22011062169447/50000000000000 : ℝ), (8524019798813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099667931/5000000000 : ℝ)|^2067 ≤ (1669722080801/12500000000000 : ℝ)^1555
        have hw : |(-1099667931/5000000000 : ℝ)|=(1099667931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394291323/10000000000 : ℝ)|^2067 ≤ (22011062169447/50000000000000 : ℝ)^1555
        have hw : |(5394291323/10000000000 : ℝ)|=(5394291323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632265507/5000000000 : ℝ)|^2067 ≤ (8524019798813/20000000000000 : ℝ)^1555
        have hw : |(2632265507/5000000000 : ℝ)|=(2632265507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672490397/5000000000 : ℝ)*x 0 + (-453034079/2000000000 : ℝ)*x 1 + (210581257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672490397/5000000000 : ℝ)^2067 ≤ (43488014069807/100000000000000 : ℝ)^1555 := by
    have hnat : (2672490397 : ℕ)^2067*100000000000000^1555 ≤ 43488014069807^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672490397 5000000000 43488014069807 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453034079/2000000000 : ℝ)^2067 ≤ (13891882500661/100000000000000 : ℝ)^1555 := by
    have hnat : (453034079 : ℕ)^2067*100000000000000^1555 ≤ 13891882500661^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453034079 2000000000 13891882500661 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210581257/400000000 : ℝ)^2067 ≤ (42620103416961/100000000000000 : ℝ)^1555 := by
    have hnat : (210581257 : ℕ)^2067*100000000000000^1555 ≤ 42620103416961^1555*400000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210581257 400000000 42620103416961 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672490397/5000000000 : ℝ), (-453034079/2000000000 : ℝ), (210581257/400000000 : ℝ)] ![(43488014069807/100000000000000 : ℝ), (13891882500661/100000000000000 : ℝ), (42620103416961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672490397/5000000000 : ℝ)|^2067 ≤ (43488014069807/100000000000000 : ℝ)^1555
        have hw : |(2672490397/5000000000 : ℝ)|=(2672490397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453034079/2000000000 : ℝ)|^2067 ≤ (13891882500661/100000000000000 : ℝ)^1555
        have hw : |(-453034079/2000000000 : ℝ)|=(453034079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210581257/400000000 : ℝ)|^2067 ≤ (42620103416961/100000000000000 : ℝ)^1555
        have hw : |(210581257/400000000 : ℝ)|=(210581257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344980931/10000000000 : ℝ)*x 0 + (2632265541/5000000000 : ℝ)*x 1 + (-453034133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344980931/10000000000 : ℝ)^2067 ≤ (8697603110297/20000000000000 : ℝ)^1555 := by
    have hnat : (5344980931 : ℕ)^2067*20000000000000^1555 ≤ 8697603110297^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344980931 10000000000 8697603110297 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632265541/5000000000 : ℝ)^2067 ≤ (21310049862917/50000000000000 : ℝ)^1555 := by
    have hnat : (2632265541 : ℕ)^2067*50000000000000^1555 ≤ 21310049862917^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632265541 5000000000 21310049862917 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453034133/2000000000 : ℝ)^2067 ≤ (3472971175433/25000000000000 : ℝ)^1555 := by
    have hnat : (453034133 : ℕ)^2067*25000000000000^1555 ≤ 3472971175433^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453034133 2000000000 3472971175433 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344980931/10000000000 : ℝ), (2632265541/5000000000 : ℝ), (-453034133/2000000000 : ℝ)] ![(8697603110297/20000000000000 : ℝ), (21310049862917/50000000000000 : ℝ), (3472971175433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344980931/10000000000 : ℝ)|^2067 ≤ (8697603110297/20000000000000 : ℝ)^1555
        have hw : |(5344980931/10000000000 : ℝ)|=(5344980931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632265541/5000000000 : ℝ)|^2067 ≤ (21310049862917/50000000000000 : ℝ)^1555
        have hw : |(2632265541/5000000000 : ℝ)|=(2632265541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453034133/2000000000 : ℝ)|^2067 ≤ (3472971175433/25000000000000 : ℝ)^1555
        have hw : |(-453034133/2000000000 : ℝ)|=(453034133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4374194797/10000000000 : ℝ)*x 0 + (4248687427/10000000000 : ℝ)*x 1 + (562931589/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374194797/10000000000 : ℝ)^2067 ≤ (4164569229013/12500000000000 : ℝ)^1555 := by
    have hnat : (4374194797 : ℕ)^2067*12500000000000^1555 ≤ 4164569229013^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374194797 10000000000 4164569229013 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248687427/10000000000 : ℝ)^2067 ≤ (256415202621/800000000000 : ℝ)^1555 := by
    have hnat : (4248687427 : ℕ)^2067*800000000000^1555 ≤ 256415202621^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248687427 10000000000 256415202621 800000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562931589/1250000000 : ℝ)^2067 ≤ (34631545832949/100000000000000 : ℝ)^1555 := by
    have hnat : (562931589 : ℕ)^2067*100000000000000^1555 ≤ 34631545832949^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562931589 1250000000 34631545832949 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374194797/10000000000 : ℝ), (4248687427/10000000000 : ℝ), (562931589/1250000000 : ℝ)] ![(4164569229013/12500000000000 : ℝ), (256415202621/800000000000 : ℝ), (34631545832949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374194797/10000000000 : ℝ)|^2067 ≤ (4164569229013/12500000000000 : ℝ)^1555
        have hw : |(4374194797/10000000000 : ℝ)|=(4374194797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248687427/10000000000 : ℝ)|^2067 ≤ (256415202621/800000000000 : ℝ)^1555
        have hw : |(4248687427/10000000000 : ℝ)|=(4248687427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562931589/1250000000 : ℝ)|^2067 ≤ (34631545832949/100000000000000 : ℝ)^1555
        have hw : |(562931589/1250000000 : ℝ)|=(562931589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-87973629/400000000 : ℝ)*x 0 + (82263389/156250000 : ℝ)*x 1 + (5393964419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87973629/400000000 : ℝ)^2067 ≤ (6678907953513/50000000000000 : ℝ)^1555 := by
    have hnat : (87973629 : ℕ)^2067*50000000000000^1555 ≤ 6678907953513^1555*400000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87973629 400000000 6678907953513 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82263389/156250000 : ℝ)^2067 ≤ (42623605944659/100000000000000 : ℝ)^1555 := by
    have hnat : (82263389 : ℕ)^2067*100000000000000^1555 ≤ 42623605944659^1555*156250000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82263389 156250000 42623605944659 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393964419/10000000000 : ℝ)^2067 ≤ (44018578144133/100000000000000 : ℝ)^1555 := by
    have hnat : (5393964419 : ℕ)^2067*100000000000000^1555 ≤ 44018578144133^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393964419 10000000000 44018578144133 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87973629/400000000 : ℝ), (82263389/156250000 : ℝ), (5393964419/10000000000 : ℝ)] ![(6678907953513/50000000000000 : ℝ), (42623605944659/100000000000000 : ℝ), (44018578144133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87973629/400000000 : ℝ)|^2067 ≤ (6678907953513/50000000000000 : ℝ)^1555
        have hw : |(-87973629/400000000 : ℝ)|=(87973629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82263389/156250000 : ℝ)|^2067 ≤ (42623605944659/100000000000000 : ℝ)^1555
        have hw : |(82263389/156250000 : ℝ)|=(82263389/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393964419/10000000000 : ℝ)|^2067 ≤ (44018578144133/100000000000000 : ℝ)^1555
        have hw : |(5393964419/10000000000 : ℝ)|=(5393964419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312273449/10000000000 : ℝ)*x 0 + (-533934379/2500000000 : ℝ)*x 1 + (5393964419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312273449/10000000000 : ℝ)^2067 ≤ (10783658822781/25000000000000 : ℝ)^1555 := by
    have hnat : (5312273449 : ℕ)^2067*25000000000000^1555 ≤ 10783658822781^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312273449 10000000000 10783658822781 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533934379/2500000000 : ℝ)^2067 ≤ (12846786553043/100000000000000 : ℝ)^1555 := by
    have hnat : (533934379 : ℕ)^2067*100000000000000^1555 ≤ 12846786553043^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533934379 2500000000 12846786553043 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393964419/10000000000 : ℝ)^2067 ≤ (44018578144133/100000000000000 : ℝ)^1555 := by
    have hnat : (5393964419 : ℕ)^2067*100000000000000^1555 ≤ 44018578144133^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393964419 10000000000 44018578144133 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312273449/10000000000 : ℝ), (-533934379/2500000000 : ℝ), (5393964419/10000000000 : ℝ)] ![(10783658822781/25000000000000 : ℝ), (12846786553043/100000000000000 : ℝ), (44018578144133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312273449/10000000000 : ℝ)|^2067 ≤ (10783658822781/25000000000000 : ℝ)^1555
        have hw : |(5312273449/10000000000 : ℝ)|=(5312273449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533934379/2500000000 : ℝ)|^2067 ≤ (12846786553043/100000000000000 : ℝ)^1555
        have hw : |(-533934379/2500000000 : ℝ)|=(533934379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393964419/10000000000 : ℝ)|^2067 ≤ (44018578144133/100000000000000 : ℝ)^1555
        have hw : |(5393964419/10000000000 : ℝ)|=(5393964419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106245469/200000000 : ℝ)*x 0 + (2696982209/5000000000 : ℝ)*x 1 + (-427147503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106245469/200000000 : ℝ)^2067 ≤ (21567317650959/50000000000000 : ℝ)^1555 := by
    have hnat : (106245469 : ℕ)^2067*50000000000000^1555 ≤ 21567317650959^1555*200000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106245469 200000000 21567317650959 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696982209/5000000000 : ℝ)^2067 ≤ (8803715626657/20000000000000 : ℝ)^1555 := by
    have hnat : (2696982209 : ℕ)^2067*20000000000000^1555 ≤ 8803715626657^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696982209 5000000000 8803715626657 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427147503/2000000000 : ℝ)^2067 ≤ (12846786545047/100000000000000 : ℝ)^1555 := by
    have hnat : (427147503 : ℕ)^2067*100000000000000^1555 ≤ 12846786545047^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427147503 2000000000 12846786545047 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106245469/200000000 : ℝ), (2696982209/5000000000 : ℝ), (-427147503/2000000000 : ℝ)] ![(21567317650959/50000000000000 : ℝ), (8803715626657/20000000000000 : ℝ), (12846786545047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106245469/200000000 : ℝ)|^2067 ≤ (21567317650959/50000000000000 : ℝ)^1555
        have hw : |(106245469/200000000 : ℝ)|=(106245469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696982209/5000000000 : ℝ)|^2067 ≤ (8803715626657/20000000000000 : ℝ)^1555
        have hw : |(2696982209/5000000000 : ℝ)|=(2696982209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427147503/2000000000 : ℝ)|^2067 ≤ (12846786545047/100000000000000 : ℝ)^1555
        have hw : |(-427147503/2000000000 : ℝ)|=(427147503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s7_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2187102437/5000000000 : ℝ)*x 0 + (4502813621/10000000000 : ℝ)*x 1 + (1062332171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187102437/5000000000 : ℝ)^2067 ≤ (6663331171273/20000000000000 : ℝ)^1555 := by
    have hnat : (2187102437 : ℕ)^2067*20000000000000^1555 ≤ 6663331171273^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187102437 5000000000 6663331171273 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502813621/10000000000 : ℝ)^2067 ≤ (34625013190199/100000000000000 : ℝ)^1555 := by
    have hnat : (4502813621 : ℕ)^2067*100000000000000^1555 ≤ 34625013190199^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502813621 10000000000 34625013190199 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062332171/2500000000 : ℝ)^2067 ≤ (3205833093501/10000000000000 : ℝ)^1555 := by
    have hnat : (1062332171 : ℕ)^2067*10000000000000^1555 ≤ 3205833093501^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062332171 2500000000 3205833093501 10000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187102437/5000000000 : ℝ), (4502813621/10000000000 : ℝ), (1062332171/2500000000 : ℝ)] ![(6663331171273/20000000000000 : ℝ), (34625013190199/100000000000000 : ℝ), (3205833093501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187102437/5000000000 : ℝ)|^2067 ≤ (6663331171273/20000000000000 : ℝ)^1555
        have hw : |(2187102437/5000000000 : ℝ)|=(2187102437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502813621/10000000000 : ℝ)|^2067 ≤ (34625013190199/100000000000000 : ℝ)^1555
        have hw : |(4502813621/10000000000 : ℝ)|=(4502813621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062332171/2500000000 : ℝ)|^2067 ≤ (3205833093501/10000000000000 : ℝ)^1555
        have hw : |(1062332171/2500000000 : ℝ)|=(1062332171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5631/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (8267/2048 : ℝ) ≤ (1480231642085461/10000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^8267 ≤ (1480231642085461/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11253 : ℕ)^8267*10000000000000000000^2048 ≤ 1480231642085461^2048*100000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 1480231642085461 10000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (1480231642085461/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (8267/2048 : ℝ) ≤ (35953819478957321/100000000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^8267 ≤ (35953819478957321/100000000000000000000 : ℝ)^2048 := by
      have hnat : (701 : ℕ)^8267*100000000000000000000^2048 ≤ 35953819478957321^2048*5000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 35953819478957321 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (35953819478957321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001480231642085461/5000000000000000000 : ℝ) ≤ (2500183329919731/2500000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (5001480231642085461/5000000000000000000 : ℝ)^2048 ≤ (2500183329919731/2500000000000000 : ℝ)^8267 := by
      have hnat : (5001480231642085461 : ℕ)^2048*2500000000000000^8267 ≤ 2500183329919731^8267*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001480231642085461 5000000000000000000 2500183329919731 2500000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500183329919731/2500000000000000 : ℝ)) (X := (5001480231642085461/5000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050756135899811931/100000000000000000000 : ℝ) ≤ (10001257151654399/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (100050756135899811931/100000000000000000000 : ℝ)^2048 ≤ (10001257151654399/10000000000000000 : ℝ)^8267 := by
      have hnat : (100050756135899811931 : ℕ)^2048*10000000000000000^8267 ≤ 10001257151654399^8267*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050756135899811931 100000000000000000000 10001257151654399 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001257151654399/10000000000000000 : ℝ)) (X := (100050756135899811931/100000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035953819478957321/50000000000000000000 : ℝ) ≤ (5000890491814937/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50035953819478957321/50000000000000000000 : ℝ)^2048 ≤ (5000890491814937/5000000000000000 : ℝ)^8267 := by
      have hnat : (50035953819478957321 : ℕ)^2048*5000000000000000^8267 ≤ 5000890491814937^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035953819478957321 50000000000000000000 5000890491814937 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000890491814937/5000000000000000 : ℝ)) (X := (50035953819478957321/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1480231642085461/10000000000000000000 : ℝ) ≤ ((13830119866555771179/13835000000000000000 : ℝ)+2*(20953279019/11068000000000 : ℝ)*(11253/100000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (13830119866555771179/13835000000000000000 : ℝ)+2*(20953279019/11068000000000 : ℝ)*(11253/100000 : ℝ)=(2500183329919731/2500000000000000 : ℝ) by norm_num, show 1+2*(1480231642085461/10000000000000000000 : ℝ)=(5001480231642085461/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35953819478957321/100000000000000000000 : ℝ)+(1480231642085461/10000000000000000000 : ℝ) ≤ ((13830119866555771179/13835000000000000000 : ℝ)+(20953279019/11068000000000 : ℝ)*((701/5000 : ℝ)+(11253/100000 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (13830119866555771179/13835000000000000000 : ℝ)+(20953279019/11068000000000 : ℝ)*((701/5000 : ℝ)+(11253/100000 : ℝ))=(10001257151654399/10000000000000000 : ℝ) by norm_num, show 1+(35953819478957321/100000000000000000000 : ℝ)+(1480231642085461/10000000000000000000 : ℝ)=(100050756135899811931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35953819478957321/100000000000000000000 : ℝ) ≤ ((13830119866555771179/13835000000000000000 : ℝ)+2*(20953279019/11068000000000 : ℝ)*(701/5000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (13830119866555771179/13835000000000000000 : ℝ)+2*(20953279019/11068000000000 : ℝ)*(701/5000 : ℝ)=(5000890491814937/5000000000000000 : ℝ) by norm_num, show 1+2*(35953819478957321/100000000000000000000 : ℝ)=(50035953819478957321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13830119866555771179/13835000000000000000 : ℝ)*(X 1 0+X 2 0)+(20953279019/11068000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (13830119866555771179/13835000000000000000 : ℝ)) (alpha := (20953279019/11068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13830119866555771179/13835000000000000000 : ℝ)*(X 0 1+X 2 1)+(20953279019/11068000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (13830119866555771179/13835000000000000000 : ℝ)) (alpha := (20953279019/11068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13830119866555771179/13835000000000000000 : ℝ)*(X 0 2+X 1 2)+(20953279019/11068000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (13830119866555771179/13835000000000000000 : ℝ)) (alpha := (20953279019/11068000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1099667931/5000000000 : ℝ)*X 0 0+(5394291323/10000000000 : ℝ)*X 0 1+(2632265507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672490397/5000000000 : ℝ)*X 1 0+(-453034079/2000000000 : ℝ)*X 1 1+(210581257/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344980931/10000000000 : ℝ)*X 2 0+(2632265541/5000000000 : ℝ)*X 2 1+(-453034133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374194797/10000000000 : ℝ)*X 0 0+(4248687427/10000000000 : ℝ)*X 0 1+(562931589/1250000000 : ℝ)*X 0 2+(4374194797/10000000000 : ℝ)*X 1 0+(4248687427/10000000000 : ℝ)*X 1 1+(562931589/1250000000 : ℝ)*X 1 2+(4374194797/10000000000 : ℝ)*X 2 0+(4248687427/10000000000 : ℝ)*X 2 1+(562931589/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-87973629/400000000 : ℝ)*X 0 0+(82263389/156250000 : ℝ)*X 0 1+(5393964419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312273449/10000000000 : ℝ)*X 1 0+(-533934379/2500000000 : ℝ)*X 1 1+(5393964419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106245469/200000000 : ℝ)*X 2 0+(2696982209/5000000000 : ℝ)*X 2 1+(-427147503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187102437/5000000000 : ℝ)*X 0 0+(4502813621/10000000000 : ℝ)*X 0 1+(1062332171/2500000000 : ℝ)*X 0 2+(2187102437/5000000000 : ℝ)*X 1 0+(4502813621/10000000000 : ℝ)*X 1 1+(1062332171/2500000000 : ℝ)*X 1 2+(2187102437/5000000000 : ℝ)*X 2 0+(4502813621/10000000000 : ℝ)*X 2 1+(1062332171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3238484218419443737300563537/691750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302325119/20000000000000 : ℝ)*(base19) + (1839016069/100000000000000 : ℝ)*(base23) + (24250221/20000000000000 : ℝ)*(upper2) + (294201029/100000000000000 : ℝ)*(upper3) + (12960633/25000000000000 : ℝ)*(upper4) + (5815935863768879/100000000000000 : ℝ)*(major0) + (5815935863768879/100000000000000 : ℝ)*(major1) + (72699198297111/1250000000000 : ℝ)*(major2) + (1926646949617263/25000000000000 : ℝ)*(sp0) + (7706643332984173/100000000000000 : ℝ)*(sp1) + (7706643005593699/100000000000000 : ℝ)*(sp2) + (1962600467649973/50000000000000 : ℝ)*(sp3) + (14261535179/25000000000000 : ℝ)*(sp4) + (5158315061/20000000000000 : ℝ)*(sp7) + (15700906907501/400000000000 : ℝ)*(f.failure) + (963330605576221/12500000000000 : ℝ)*(f.sum) + (18440679082567/5534000000000000000000000000 : ℝ)*base66 + (4501239545268838341/1383500000000000000000000000000000 : ℝ)*base67 + (46651498054604003/8646875000000000000000000000000 : ℝ)*base70 + (7539724836316338341/1383500000000000000000000000000000 : ℝ)*base71 + (343740125697/5534000000000000000000000000 : ℝ)*base73 + (59823230410475439/4323437500000000000000000000000 : ℝ)*base76 + (28592745955541911659/1383500000000000000000000000000000 : ℝ)*base78 + (5108360309364088341/1383500000000000000000000000000000 : ℝ)*base79 + (5175437618987/1383500000000000000000000000 : ℝ)*base82 + (399349/40000000000000000000 : ℝ)*base90 + (399349/40000000000000000000 : ℝ)*base92 + (799349/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7510637180373054914445975633/691750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (784753/39062500000 : ℝ)*(base19) + (68325531/3125000000000 : ℝ)*(base23) + (217200169/100000000000000 : ℝ)*(upper3) + (79895279/100000000000000 : ℝ)*(lower4) + (110365951/50000000000000 : ℝ)*(upper5) + (5845243709702591/100000000000000 : ℝ)*(major0) + (5845243709702591/100000000000000 : ℝ)*(major1) + (5845243709702591/100000000000000 : ℝ)*(major2) + (54710740301/100000000000000 : ℝ)*(sp1) + (58867390669/100000000000000 : ℝ)*(sp2) + (7745480205307537/100000000000000 : ℝ)*(sp4) + (7745423485599557/100000000000000 : ℝ)*(sp5) + (61963353211999/800000000000 : ℝ)*(sp6) + (1972503426091411/50000000000000 : ℝ)*(sp7) + (1972503426091411/50000000000000 : ℝ)*(f.failure) + (7745480205307537/100000000000000 : ℝ)*(f.sum) + (108752587741/172937500000000000000000000 : ℝ)*base66 + (7560094493443325211/1383500000000000000000000000000000 : ℝ)*base68 + (186331417267174789/1383500000000000000000000000000000 : ℝ)*base69 + (2298073631523174789/1383500000000000000000000000000000 : ℝ)*base71 + (948842196037/138350000000000000000000000 : ℝ)*base74 + (12871273437200325211/1383500000000000000000000000000000 : ℝ)*base76 + (12938419252006174789/1383500000000000000000000000000000 : ℝ)*base77 + (8635853159680674789/1383500000000000000000000000000000 : ℝ)*base79 + (10621836460901/2767000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (25148939/5000000000000000000000 : ℝ)*base90 + (25148939/5000000000000000000000 : ℝ)*base92 + (25148939/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1075_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1075_s8_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-549835651/2500000000 : ℝ)*x 0 + (337137259/625000000 : ℝ)*x 1 + (2632310951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549835651/2500000000 : ℝ)^2067 ≤ (6678915538413/50000000000000 : ℝ)^1555 := by
    have hnat : (549835651 : ℕ)^2067*50000000000000^1555 ≤ 6678915538413^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549835651 2500000000 6678915538413 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337137259/625000000 : ℝ)^2067 ≤ (2201054592361/5000000000000 : ℝ)^1555 := by
    have hnat : (337137259 : ℕ)^2067*5000000000000^1555 ≤ 2201054592361^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337137259 625000000 2201054592361 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632310951/5000000000 : ℝ)^2067 ≤ (2663817316883/6250000000000 : ℝ)^1555 := by
    have hnat : (2632310951 : ℕ)^2067*6250000000000^1555 ≤ 2663817316883^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632310951 5000000000 2663817316883 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549835651/2500000000 : ℝ), (337137259/625000000 : ℝ), (2632310951/5000000000 : ℝ)] ![(6678915538413/50000000000000 : ℝ), (2201054592361/5000000000000 : ℝ), (2663817316883/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549835651/2500000000 : ℝ)|^2067 ≤ (6678915538413/50000000000000 : ℝ)^1555
        have hw : |(-549835651/2500000000 : ℝ)|=(549835651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337137259/625000000 : ℝ)|^2067 ≤ (2201054592361/5000000000000 : ℝ)^1555
        have hw : |(337137259/625000000 : ℝ)|=(337137259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632310951/5000000000 : ℝ)|^2067 ≤ (2663817316883/6250000000000 : ℝ)^1555
        have hw : |(2632310951/5000000000 : ℝ)|=(2632310951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344957389/10000000000 : ℝ)*x 0 + (-453016403/2000000000 : ℝ)*x 1 + (2632310949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344957389/10000000000 : ℝ)^2067 ≤ (21743880470421/50000000000000 : ℝ)^1555 := by
    have hnat : (5344957389 : ℕ)^2067*50000000000000^1555 ≤ 21743880470421^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344957389 10000000000 21743880470421 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453016403/2000000000 : ℝ)^2067 ≤ (3472790505337/25000000000000 : ℝ)^1555 := by
    have hnat : (453016403 : ℕ)^2067*25000000000000^1555 ≤ 3472790505337^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453016403 2000000000 3472790505337 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632310949/5000000000 : ℝ)^2067 ≤ (21310538513541/50000000000000 : ℝ)^1555 := by
    have hnat : (2632310949 : ℕ)^2067*50000000000000^1555 ≤ 21310538513541^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632310949 5000000000 21310538513541 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344957389/10000000000 : ℝ), (-453016403/2000000000 : ℝ), (2632310949/5000000000 : ℝ)] ![(21743880470421/50000000000000 : ℝ), (3472790505337/25000000000000 : ℝ), (21310538513541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344957389/10000000000 : ℝ)|^2067 ≤ (21743880470421/50000000000000 : ℝ)^1555
        have hw : |(5344957389/10000000000 : ℝ)|=(5344957389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453016403/2000000000 : ℝ)|^2067 ≤ (3472790505337/25000000000000 : ℝ)^1555
        have hw : |(-453016403/2000000000 : ℝ)|=(453016403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632310949/5000000000 : ℝ)|^2067 ≤ (21310538513541/50000000000000 : ℝ)^1555
        have hw : |(2632310949/5000000000 : ℝ)|=(2632310949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668119673/1250000000 : ℝ)*x 0 + (2632310943/5000000000 : ℝ)*x 1 + (-2265082037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668119673/1250000000 : ℝ)^2067 ≤ (21743880443383/50000000000000 : ℝ)^1555 := by
    have hnat : (668119673 : ℕ)^2067*50000000000000^1555 ≤ 21743880443383^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668119673 1250000000 21743880443383 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632310943/5000000000 : ℝ)^2067 ≤ (21310538448973/50000000000000 : ℝ)^1555 := by
    have hnat : (2632310943 : ℕ)^2067*50000000000000^1555 ≤ 21310538448973^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632310943 5000000000 21310538448973 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265082037/10000000000 : ℝ)^2067 ≤ (13891162200693/100000000000000 : ℝ)^1555 := by
    have hnat : (2265082037 : ℕ)^2067*100000000000000^1555 ≤ 13891162200693^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265082037 10000000000 13891162200693 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668119673/1250000000 : ℝ), (2632310943/5000000000 : ℝ), (-2265082037/10000000000 : ℝ)] ![(21743880443383/50000000000000 : ℝ), (21310538448973/50000000000000 : ℝ), (13891162200693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668119673/1250000000 : ℝ)|^2067 ≤ (21743880443383/50000000000000 : ℝ)^1555
        have hw : |(668119673/1250000000 : ℝ)|=(668119673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632310943/5000000000 : ℝ)|^2067 ≤ (21310538448973/50000000000000 : ℝ)^1555
        have hw : |(2632310943/5000000000 : ℝ)|=(2632310943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2265082037/10000000000 : ℝ)|^2067 ≤ (13891162200693/100000000000000 : ℝ)^1555
        have hw : |(-2265082037/10000000000 : ℝ)|=(2265082037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2187099833/5000000000 : ℝ)*x 0 + (849773747/2000000000 : ℝ)*x 1 + (2251635011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187099833/5000000000 : ℝ)^2067 ≤ (33316603128127/100000000000000 : ℝ)^1555 := by
    have hnat : (2187099833 : ℕ)^2067*100000000000000^1555 ≤ 33316603128127^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187099833 5000000000 33316603128127 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849773747/2000000000 : ℝ)^2067 ≤ (6410743695017/20000000000000 : ℝ)^1555 := by
    have hnat : (849773747 : ℕ)^2067*20000000000000^1555 ≤ 6410743695017^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849773747 2000000000 6410743695017 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251635011/5000000000 : ℝ)^2067 ≤ (34629678386189/100000000000000 : ℝ)^1555 := by
    have hnat : (2251635011 : ℕ)^2067*100000000000000^1555 ≤ 34629678386189^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251635011 5000000000 34629678386189 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187099833/5000000000 : ℝ), (849773747/2000000000 : ℝ), (2251635011/5000000000 : ℝ)] ![(33316603128127/100000000000000 : ℝ), (6410743695017/20000000000000 : ℝ), (34629678386189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187099833/5000000000 : ℝ)|^2067 ≤ (33316603128127/100000000000000 : ℝ)^1555
        have hw : |(2187099833/5000000000 : ℝ)|=(2187099833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849773747/2000000000 : ℝ)|^2067 ≤ (6410743695017/20000000000000 : ℝ)^1555
        have hw : |(849773747/2000000000 : ℝ)|=(849773747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251635011/5000000000 : ℝ)|^2067 ≤ (34629678386189/100000000000000 : ℝ)^1555
        have hw : |(2251635011/5000000000 : ℝ)|=(2251635011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199347647/10000000000 : ℝ)*x 0 + (5264946519/10000000000 : ℝ)*x 1 + (2696935177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199347647/10000000000 : ℝ)^2067 ≤ (6678935895343/50000000000000 : ℝ)^1555 := by
    have hnat : (2199347647 : ℕ)^2067*50000000000000^1555 ≤ 6678935895343^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199347647 10000000000 6678935895343 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264946519/10000000000 : ℝ)^2067 ≤ (21312285213627/50000000000000 : ℝ)^1555 := by
    have hnat : (5264946519 : ℕ)^2067*50000000000000^1555 ≤ 21312285213627^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264946519 10000000000 21312285213627 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696935177/5000000000 : ℝ)^2067 ≤ (44017557757339/100000000000000 : ℝ)^1555 := by
    have hnat : (2696935177 : ℕ)^2067*100000000000000^1555 ≤ 44017557757339^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696935177 5000000000 44017557757339 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199347647/10000000000 : ℝ), (5264946519/10000000000 : ℝ), (2696935177/5000000000 : ℝ)] ![(6678935895343/50000000000000 : ℝ), (21312285213627/50000000000000 : ℝ), (44017557757339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199347647/10000000000 : ℝ)|^2067 ≤ (6678935895343/50000000000000 : ℝ)^1555
        have hw : |(-2199347647/10000000000 : ℝ)|=(2199347647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264946519/10000000000 : ℝ)|^2067 ≤ (21312285213627/50000000000000 : ℝ)^1555
        have hw : |(5264946519/10000000000 : ℝ)|=(5264946519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696935177/5000000000 : ℝ)|^2067 ≤ (44017557757339/100000000000000 : ℝ)^1555
        have hw : |(2696935177/5000000000 : ℝ)|=(2696935177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312296821/10000000000 : ℝ)*x 0 + (-266979197/1250000000 : ℝ)*x 1 + (5393870359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312296821/10000000000 : ℝ)^2067 ≤ (43134887553211/100000000000000 : ℝ)^1555 := by
    have hnat : (5312296821 : ℕ)^2067*100000000000000^1555 ≤ 43134887553211^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312296821 10000000000 43134887553211 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266979197/1250000000 : ℝ)^2067 ≤ (12847554626069/100000000000000 : ℝ)^1555 := by
    have hnat : (266979197 : ℕ)^2067*100000000000000^1555 ≤ 12847554626069^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266979197 1250000000 12847554626069 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393870359/10000000000 : ℝ)^2067 ≤ (44017557811577/100000000000000 : ℝ)^1555 := by
    have hnat : (5393870359 : ℕ)^2067*100000000000000^1555 ≤ 44017557811577^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393870359 10000000000 44017557811577 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312296821/10000000000 : ℝ), (-266979197/1250000000 : ℝ), (5393870359/10000000000 : ℝ)] ![(43134887553211/100000000000000 : ℝ), (12847554626069/100000000000000 : ℝ), (44017557811577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312296821/10000000000 : ℝ)|^2067 ≤ (43134887553211/100000000000000 : ℝ)^1555
        have hw : |(5312296821/10000000000 : ℝ)|=(5312296821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266979197/1250000000 : ℝ)|^2067 ≤ (12847554626069/100000000000000 : ℝ)^1555
        have hw : |(-266979197/1250000000 : ℝ)|=(266979197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393870359/10000000000 : ℝ)|^2067 ≤ (44017557811577/100000000000000 : ℝ)^1555
        have hw : |(5393870359/10000000000 : ℝ)|=(5393870359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312296823/10000000000 : ℝ)*x 0 + (5393870357/10000000000 : ℝ)*x 1 + (-85433343/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312296823/10000000000 : ℝ)^2067 ≤ (21567443787399/50000000000000 : ℝ)^1555 := by
    have hnat : (5312296823 : ℕ)^2067*50000000000000^1555 ≤ 21567443787399^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312296823 10000000000 21567443787399 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393870357/10000000000 : ℝ)^2067 ≤ (22008778894941/50000000000000 : ℝ)^1555 := by
    have hnat : (5393870357 : ℕ)^2067*50000000000000^1555 ≤ 22008778894941^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393870357 10000000000 22008778894941 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85433343/400000000 : ℝ)^2067 ≤ (12847554618073/100000000000000 : ℝ)^1555 := by
    have hnat : (85433343 : ℕ)^2067*100000000000000^1555 ≤ 12847554618073^1555*400000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85433343 400000000 12847554618073 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312296823/10000000000 : ℝ), (5393870357/10000000000 : ℝ), (-85433343/400000000 : ℝ)] ![(21567443787399/50000000000000 : ℝ), (22008778894941/50000000000000 : ℝ), (12847554618073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312296823/10000000000 : ℝ)|^2067 ≤ (21567443787399/50000000000000 : ℝ)^1555
        have hw : |(5312296823/10000000000 : ℝ)|=(5312296823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393870357/10000000000 : ℝ)|^2067 ≤ (22008778894941/50000000000000 : ℝ)^1555
        have hw : |(5393870357/10000000000 : ℝ)|=(5393870357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85433343/400000000 : ℝ)|^2067 ≤ (12847554618073/100000000000000 : ℝ)^1555
        have hw : |(-85433343/400000000 : ℝ)|=(85433343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s8_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (218710479/500000000 : ℝ)*x 0 + (2251316329/5000000000 : ℝ)*x 1 + (212475419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218710479/500000000 : ℝ)^2067 ≤ (33316703502137/100000000000000 : ℝ)^1555 := by
    have hnat : (218710479 : ℕ)^2067*100000000000000^1555 ≤ 33316703502137^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218710479 500000000 33316703502137 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251316329/5000000000 : ℝ)^2067 ≤ (2163947717691/6250000000000 : ℝ)^1555 := by
    have hnat : (2251316329 : ℕ)^2067*6250000000000^1555 ≤ 2163947717691^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251316329 5000000000 2163947717691 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212475419/500000000 : ℝ)^2067 ≤ (32060133006847/100000000000000 : ℝ)^1555 := by
    have hnat : (212475419 : ℕ)^2067*100000000000000^1555 ≤ 32060133006847^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212475419 500000000 32060133006847 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218710479/500000000 : ℝ), (2251316329/5000000000 : ℝ), (212475419/500000000 : ℝ)] ![(33316703502137/100000000000000 : ℝ), (2163947717691/6250000000000 : ℝ), (32060133006847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218710479/500000000 : ℝ)|^2067 ≤ (33316703502137/100000000000000 : ℝ)^1555
        have hw : |(218710479/500000000 : ℝ)|=(218710479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251316329/5000000000 : ℝ)|^2067 ≤ (2163947717691/6250000000000 : ℝ)^1555
        have hw : |(2251316329/5000000000 : ℝ)|=(2251316329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212475419/500000000 : ℝ)|^2067 ≤ (32060133006847/100000000000000 : ℝ)^1555
        have hw : |(212475419/500000000 : ℝ)|=(212475419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (352/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5631/50000 : ℝ) ^ (8267/2048 : ℝ) ≤ (2970032562704231/20000000000000000000 : ℝ) := by
    have hpowers : (5631/50000 : ℝ)^8267 ≤ (2970032562704231/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5631 : ℕ)^8267*20000000000000000000^2048 ≤ 2970032562704231^2048*50000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5631 50000 2970032562704231 20000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5631/50000 : ℝ)) (X := (2970032562704231/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (8267/2048 : ℝ) ≤ (35860744231080681/100000000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^8267 ≤ (35860744231080681/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14011 : ℕ)^8267*100000000000000000000^2048 ≤ 35860744231080681^2048*100000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 35860744231080681 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (35860744231080681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002970032562704231/10000000000000000000 : ℝ) ≤ (10000735689766253/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (10002970032562704231/10000000000000000000 : ℝ)^2048 ≤ (10000735689766253/10000000000000000 : ℝ)^8267 := by
      have hnat : (10002970032562704231 : ℕ)^2048*10000000000000000^8267 ≤ 10000735689766253^8267*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002970032562704231 10000000000000000000 10000735689766253 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000735689766253/10000000000000000 : ℝ)) (X := (10002970032562704231/10000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012677726761150459/25000000000000000000 : ℝ) ≤ (10001256031618603/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (25012677726761150459/25000000000000000000 : ℝ)^2048 ≤ (10001256031618603/10000000000000000 : ℝ)^8267 := by
      have hnat : (25012677726761150459 : ℕ)^2048*10000000000000000^8267 ≤ 10001256031618603^8267*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012677726761150459 25000000000000000000 10001256031618603 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001256031618603/10000000000000000 : ℝ)) (X := (25012677726761150459/25000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035860744231080681/50000000000000000000 : ℝ) ≤ (10001776373470953/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50035860744231080681/50000000000000000000 : ℝ)^2048 ≤ (10001776373470953/10000000000000000 : ℝ)^8267 := by
      have hnat : (50035860744231080681 : ℕ)^2048*10000000000000000^8267 ≤ 10001776373470953^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035860744231080681 50000000000000000000 10001776373470953 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001776373470953/10000000000000000 : ℝ)) (X := (50035860744231080681/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2970032562704231/20000000000000000000 : ℝ) ≤ ((27480302231285098097/27490000000000000000 : ℝ)+2*(10406837047/5498000000000 : ℝ)*(5631/50000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (27480302231285098097/27490000000000000000 : ℝ)+2*(10406837047/5498000000000 : ℝ)*(5631/50000 : ℝ)=(10000735689766253/10000000000000000 : ℝ) by norm_num, show 1+2*(2970032562704231/20000000000000000000 : ℝ)=(10002970032562704231/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35860744231080681/100000000000000000000 : ℝ)+(2970032562704231/20000000000000000000 : ℝ) ≤ ((27480302231285098097/27490000000000000000 : ℝ)+(10406837047/5498000000000 : ℝ)*((14011/100000 : ℝ)+(5631/50000 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (27480302231285098097/27490000000000000000 : ℝ)+(10406837047/5498000000000 : ℝ)*((14011/100000 : ℝ)+(5631/50000 : ℝ))=(10001256031618603/10000000000000000 : ℝ) by norm_num, show 1+(35860744231080681/100000000000000000000 : ℝ)+(2970032562704231/20000000000000000000 : ℝ)=(25012677726761150459/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35860744231080681/100000000000000000000 : ℝ) ≤ ((27480302231285098097/27490000000000000000 : ℝ)+2*(10406837047/5498000000000 : ℝ)*(14011/100000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (27480302231285098097/27490000000000000000 : ℝ)+2*(10406837047/5498000000000 : ℝ)*(14011/100000 : ℝ)=(10001776373470953/10000000000000000 : ℝ) by norm_num, show 1+2*(35860744231080681/100000000000000000000 : ℝ)=(50035860744231080681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27480302231285098097/27490000000000000000 : ℝ)*(X 1 0+X 2 0)+(10406837047/5498000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (27480302231285098097/27490000000000000000 : ℝ)) (alpha := (10406837047/5498000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27480302231285098097/27490000000000000000 : ℝ)*(X 0 1+X 2 1)+(10406837047/5498000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (27480302231285098097/27490000000000000000 : ℝ)) (alpha := (10406837047/5498000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27480302231285098097/27490000000000000000 : ℝ)*(X 0 2+X 1 2)+(10406837047/5498000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (27480302231285098097/27490000000000000000 : ℝ)) (alpha := (10406837047/5498000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549835651/2500000000 : ℝ)*X 0 0+(337137259/625000000 : ℝ)*X 0 1+(2632310951/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344957389/10000000000 : ℝ)*X 1 0+(-453016403/2000000000 : ℝ)*X 1 1+(2632310949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668119673/1250000000 : ℝ)*X 2 0+(2632310943/5000000000 : ℝ)*X 2 1+(-2265082037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187099833/5000000000 : ℝ)*X 0 0+(849773747/2000000000 : ℝ)*X 0 1+(2251635011/5000000000 : ℝ)*X 0 2+(2187099833/5000000000 : ℝ)*X 1 0+(849773747/2000000000 : ℝ)*X 1 1+(2251635011/5000000000 : ℝ)*X 1 2+(2187099833/5000000000 : ℝ)*X 2 0+(849773747/2000000000 : ℝ)*X 2 1+(2251635011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2199347647/10000000000 : ℝ)*X 0 0+(5264946519/10000000000 : ℝ)*X 0 1+(2696935177/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312296821/10000000000 : ℝ)*X 1 0+(-266979197/1250000000 : ℝ)*X 1 1+(5393870359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312296823/10000000000 : ℝ)*X 2 0+(5393870357/10000000000 : ℝ)*X 2 1+(-85433343/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218710479/500000000 : ℝ)*X 0 0+(2251316329/5000000000 : ℝ)*X 0 1+(212475419/500000000 : ℝ)*X 0 2+(218710479/500000000 : ℝ)*X 1 0+(2251316329/5000000000 : ℝ)*X 1 1+(212475419/500000000 : ℝ)*X 1 2+(218710479/500000000 : ℝ)*X 2 0+(2251316329/5000000000 : ℝ)*X 2 1+(212475419/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (627175193370394165203/109960000000000000000000000 : ℝ) := by norm_num
    linear_combination (585022149/50000000000000 : ℝ)*(base19) + (1089215249/100000000000000 : ℝ)*(base23) + (983599/2500000000000 : ℝ)*(lower2) + (32316709/20000000000000 : ℝ)*(upper3) + (35208541/50000000000000 : ℝ)*(upper5) + (2912119311362467/50000000000000 : ℝ)*(major0) + (2912119311362467/50000000000000 : ℝ)*(major1) + (1164847724544987/20000000000000 : ℝ)*(major2) + (482351037220947/6250000000000 : ℝ)*(sp0) + (7717645552707391/100000000000000 : ℝ)*(sp1) + (7717645633536441/100000000000000 : ℝ)*(sp2) + (196540644320231/5000000000000 : ℝ)*(sp3) + (30127216537/100000000000000 : ℝ)*(sp4) + (17446171329/100000000000000 : ℝ)*(sp7) + (3930830332575949/100000000000000 : ℝ)*(f.failure) + (7717646722751689/100000000000000 : ℝ)*(f.sum) + (2542063481479/1374500000000000000000000000 : ℝ)*base65 + (7358263150307074701/1374500000000000000000000000000000 : ℝ)*base68 + (3591737815154989739/549800000000000000000000000000000 : ℝ)*base69 + (14169988705975925299/1374500000000000000000000000000000 : ℝ)*base71 + (3629731296109/1374500000000000000000000000 : ℝ)*base74 + (1769969467661810261/549800000000000000000000000000000 : ℝ)*base76 + (14314865610605925299/1374500000000000000000000000000000 : ℝ)*base77 + (92432848982074701/1374500000000000000000000000000000 : ℝ)*base80 + (300530884073/2749000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (30400299/10000000000000000000000 : ℝ)*base89 + (30400299/10000000000000000000000 : ℝ)*base91 + (69599701/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7421004634080341951667/687250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1994408969/100000000000000 : ℝ)*(base19) + (17410213/800000000000 : ℝ)*(base23) + (351539347/50000000000000 : ℝ)*(lower1) + (109725077/50000000000000 : ℝ)*(upper3) + (81718811/100000000000000 : ℝ)*(lower4) + (227622611/100000000000000 : ℝ)*(upper5) + (5853530873753623/100000000000000 : ℝ)*(major0) + (5853530873753623/100000000000000 : ℝ)*(major1) + (5853530873753623/100000000000000 : ℝ)*(major2) + (1021368829/25000000000000 : ℝ)*(sp2) + (969557681853291/12500000000000 : ℝ)*(sp4) + (7756459460417359/100000000000000 : ℝ)*(sp5) + (3878227596537193/50000000000000 : ℝ)*(sp6) + (1975299966371863/50000000000000 : ℝ)*(sp7) + (1975299966371863/50000000000000 : ℝ)*(f.failure) + (969557681853291/12500000000000 : ℝ)*(f.sum) + (1928009490837/1374500000000000000000000000 : ℝ)*base65 + (22213942295509155431/2749000000000000000000000000000000 : ℝ)*base67 + (7220832399438844569/2749000000000000000000000000000000 : ℝ)*base70 + (70894288766861844569/2749000000000000000000000000000000 : ℝ)*base72 + (5264904410133/1374500000000000000000000000 : ℝ)*base74 + (270193695982419844569/2749000000000000000000000000000000 : ℝ)*base76 + (16508810198171155431/2749000000000000000000000000000000 : ℝ)*base77 + (37843135633555155431/2749000000000000000000000000000000 : ℝ)*base79 + (2760496605887/687250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (30864687/5000000000000000000000 : ℝ)*base90 + (30864687/5000000000000000000000 : ℝ)*base92 + (30864687/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1075_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1075_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1075_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1075_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1075_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
