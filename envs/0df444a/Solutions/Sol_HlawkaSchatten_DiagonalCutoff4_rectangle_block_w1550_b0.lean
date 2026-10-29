-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:32.149252+00:00
-- url     : https://prove2.me/submissions/3bcd98f9-9ed8-4b96-b336-68566a3d0cf8

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
theorem support_rectangle_w1550_s0_0 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41156557/250000000 : ℝ)*x 0 + (5884164123/10000000000 : ℝ)*x 1 + (2435619129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41156557/250000000 : ℝ)^4597 ≤ (1963280824693/20000000000000 : ℝ)^3573 := by
    have hnat : (41156557 : ℕ)^4597*20000000000000^3573 ≤ 1963280824693^3573*250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41156557 250000000 1963280824693 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5884164123/10000000000 : ℝ)^4597 ≤ (50544958025129/100000000000000 : ℝ)^3573 := by
    have hnat : (5884164123 : ℕ)^4597*100000000000000^3573 ≤ 50544958025129^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5884164123 10000000000 50544958025129 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435619129/5000000000 : ℝ)^4597 ≤ (19819318918983/50000000000000 : ℝ)^3573 := by
    have hnat : (2435619129 : ℕ)^4597*50000000000000^3573 ≤ 19819318918983^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435619129 5000000000 19819318918983 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41156557/250000000 : ℝ), (5884164123/10000000000 : ℝ), (2435619129/5000000000 : ℝ)] ![(1963280824693/20000000000000 : ℝ), (50544958025129/100000000000000 : ℝ), (19819318918983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41156557/250000000 : ℝ)|^4597 ≤ (1963280824693/20000000000000 : ℝ)^3573
        have hw : |(-41156557/250000000 : ℝ)|=(41156557/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5884164123/10000000000 : ℝ)|^4597 ≤ (50544958025129/100000000000000 : ℝ)^3573
        have hw : |(5884164123/10000000000 : ℝ)|=(5884164123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435619129/5000000000 : ℝ)|^4597 ≤ (19819318918983/50000000000000 : ℝ)^3573
        have hw : |(2435619129/5000000000 : ℝ)|=(2435619129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_1 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093952173/2000000000 : ℝ)*x 0 + (-69103513/312500000 : ℝ)*x 1 + (974247651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093952173/2000000000 : ℝ)^4597 ≤ (1437876832159/3125000000000 : ℝ)^3573 := by
    have hnat : (1093952173 : ℕ)^4597*3125000000000^3573 ≤ 1437876832159^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093952173 2000000000 1437876832159 3125000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69103513/312500000 : ℝ)^4597 ≤ (14349303546737/100000000000000 : ℝ)^3573 := by
    have hnat : (69103513 : ℕ)^4597*100000000000000^3573 ≤ 14349303546737^3573*312500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69103513 312500000 14349303546737 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974247651/2000000000 : ℝ)^4597 ≤ (19819318903279/50000000000000 : ℝ)^3573 := by
    have hnat : (974247651 : ℕ)^4597*50000000000000^3573 ≤ 19819318903279^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974247651 2000000000 19819318903279 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093952173/2000000000 : ℝ), (-69103513/312500000 : ℝ), (974247651/2000000000 : ℝ)] ![(1437876832159/3125000000000 : ℝ), (14349303546737/100000000000000 : ℝ), (19819318903279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093952173/2000000000 : ℝ)|^4597 ≤ (1437876832159/3125000000000 : ℝ)^3573
        have hw : |(1093952173/2000000000 : ℝ)|=(1093952173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69103513/312500000 : ℝ)|^4597 ≤ (14349303546737/100000000000000 : ℝ)^3573
        have hw : |(-69103513/312500000 : ℝ)|=(69103513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974247651/2000000000 : ℝ)|^4597 ≤ (19819318903279/50000000000000 : ℝ)^3573
        have hw : |(974247651/2000000000 : ℝ)|=(974247651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_2 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5469760899/10000000000 : ℝ)*x 0 + (608904777/1250000000 : ℝ)*x 1 + (-1105656211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5469760899/10000000000 : ℝ)^4597 ≤ (11503014749267/25000000000000 : ℝ)^3573 := by
    have hnat : (5469760899 : ℕ)^4597*25000000000000^3573 ≤ 11503014749267^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469760899 10000000000 11503014749267 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608904777/1250000000 : ℝ)^4597 ≤ (9909659349563/25000000000000 : ℝ)^3573 := by
    have hnat : (608904777 : ℕ)^4597*25000000000000^3573 ≤ 9909659349563^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608904777 1250000000 9909659349563 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105656211/5000000000 : ℝ)^4597 ≤ (14349303596829/100000000000000 : ℝ)^3573 := by
    have hnat : (1105656211 : ℕ)^4597*100000000000000^3573 ≤ 14349303596829^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105656211 5000000000 14349303596829 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5469760899/10000000000 : ℝ), (608904777/1250000000 : ℝ), (-1105656211/5000000000 : ℝ)] ![(11503014749267/25000000000000 : ℝ), (9909659349563/25000000000000 : ℝ), (14349303596829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5469760899/10000000000 : ℝ)|^4597 ≤ (11503014749267/25000000000000 : ℝ)^3573
        have hw : |(5469760899/10000000000 : ℝ)|=(5469760899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608904777/1250000000 : ℝ)|^4597 ≤ (9909659349563/25000000000000 : ℝ)^3573
        have hw : |(608904777/1250000000 : ℝ)|=(608904777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105656211/5000000000 : ℝ)|^4597 ≤ (14349303596829/100000000000000 : ℝ)^3573
        have hw : |(-1105656211/5000000000 : ℝ)|=(1105656211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_3 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067524413/5000000000 : ℝ)*x 0 + (48315619/156250000 : ℝ)*x 1 + (5450730927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067524413/5000000000 : ℝ)^4597 ≤ (32104531301143/100000000000000 : ℝ)^3573 := by
    have hnat : (2067524413 : ℕ)^4597*100000000000000^3573 ≤ 32104531301143^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067524413 5000000000 32104531301143 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48315619/156250000 : ℝ)^4597 ≤ (22089266950649/100000000000000 : ℝ)^3573 := by
    have hnat : (48315619 : ℕ)^4597*100000000000000^3573 ≤ 22089266950649^3573*156250000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48315619 156250000 22089266950649 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450730927/10000000000 : ℝ)^4597 ≤ (17893047549/39062500000 : ℝ)^3573 := by
    have hnat : (5450730927 : ℕ)^4597*39062500000^3573 ≤ 17893047549^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450730927 10000000000 17893047549 39062500000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067524413/5000000000 : ℝ), (48315619/156250000 : ℝ), (5450730927/10000000000 : ℝ)] ![(32104531301143/100000000000000 : ℝ), (22089266950649/100000000000000 : ℝ), (17893047549/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067524413/5000000000 : ℝ)|^4597 ≤ (32104531301143/100000000000000 : ℝ)^3573
        have hw : |(2067524413/5000000000 : ℝ)|=(2067524413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48315619/156250000 : ℝ)|^4597 ≤ (22089266950649/100000000000000 : ℝ)^3573
        have hw : |(48315619/156250000 : ℝ)|=(48315619/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450730927/10000000000 : ℝ)|^4597 ≤ (17893047549/39062500000 : ℝ)^3573
        have hw : |(5450730927/10000000000 : ℝ)|=(5450730927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_4 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649471453/10000000000 : ℝ)*x 0 + (4896877431/10000000000 : ℝ)*x 1 + (45762597/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649471453/10000000000 : ℝ)^4597 ≤ (9841030995913/100000000000000 : ℝ)^3573 := by
    have hnat : (1649471453 : ℕ)^4597*100000000000000^3573 ≤ 9841030995913^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649471453 10000000000 9841030995913 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4896877431/10000000000 : ℝ)^4597 ≤ (399072662063/1000000000000 : ℝ)^3573 := by
    have hnat : (4896877431 : ℕ)^4597*1000000000000^3573 ≤ 399072662063^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4896877431 10000000000 399072662063 1000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45762597/78125000 : ℝ)^4597 ≤ (50251702783443/100000000000000 : ℝ)^3573 := by
    have hnat : (45762597 : ℕ)^4597*100000000000000^3573 ≤ 50251702783443^3573*78125000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45762597 78125000 50251702783443 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649471453/10000000000 : ℝ), (4896877431/10000000000 : ℝ), (45762597/78125000 : ℝ)] ![(9841030995913/100000000000000 : ℝ), (399072662063/1000000000000 : ℝ), (50251702783443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649471453/10000000000 : ℝ)|^4597 ≤ (9841030995913/100000000000000 : ℝ)^3573
        have hw : |(-1649471453/10000000000 : ℝ)|=(1649471453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4896877431/10000000000 : ℝ)|^4597 ≤ (399072662063/1000000000000 : ℝ)^3573
        have hw : |(4896877431/10000000000 : ℝ)|=(4896877431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(45762597/78125000 : ℝ)|^4597 ≤ (50251702783443/100000000000000 : ℝ)^3573
        have hw : |(45762597/78125000 : ℝ)|=(45762597/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_5 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324555659/625000000 : ℝ)*x 0 + (-7655867/62500000 : ℝ)*x 1 + (5857612043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324555659/625000000 : ℝ)^4597 ≤ (5379689197057/12500000000000 : ℝ)^3573 := by
    have hnat : (324555659 : ℕ)^4597*12500000000000^3573 ≤ 5379689197057^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324555659 625000000 5379689197057 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7655867/62500000 : ℝ)^4597 ≤ (838848468339/12500000000000 : ℝ)^3573 := by
    have hnat : (7655867 : ℕ)^4597*12500000000000^3573 ≤ 838848468339^3573*62500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7655867 62500000 838848468339 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5857612043/10000000000 : ℝ)^4597 ≤ (50251698666447/100000000000000 : ℝ)^3573 := by
    have hnat : (5857612043 : ℕ)^4597*100000000000000^3573 ≤ 50251698666447^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857612043 10000000000 50251698666447 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324555659/625000000 : ℝ), (-7655867/62500000 : ℝ), (5857612043/10000000000 : ℝ)] ![(5379689197057/12500000000000 : ℝ), (838848468339/12500000000000 : ℝ), (50251698666447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324555659/625000000 : ℝ)|^4597 ≤ (5379689197057/12500000000000 : ℝ)^3573
        have hw : |(324555659/625000000 : ℝ)|=(324555659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7655867/62500000 : ℝ)|^4597 ≤ (838848468339/12500000000000 : ℝ)^3573
        have hw : |(-7655867/62500000 : ℝ)|=(7655867/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5857612043/10000000000 : ℝ)|^4597 ≤ (50251698666447/100000000000000 : ℝ)^3573
        have hw : |(5857612043/10000000000 : ℝ)|=(5857612043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_6 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41543119/80000000 : ℝ)*x 0 + (2928806571/5000000000 : ℝ)*x 1 + (-306234503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41543119/80000000 : ℝ)^4597 ≤ (10759376610727/25000000000000 : ℝ)^3573 := by
    have hnat : (41543119 : ℕ)^4597*25000000000000^3573 ≤ 10759376610727^3573*80000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41543119 80000000 10759376610727 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2928806571/5000000000 : ℝ)^4597 ≤ (10050342159337/20000000000000 : ℝ)^3573 := by
    have hnat : (2928806571 : ℕ)^4597*20000000000000^3573 ≤ 10050342159337^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2928806571 5000000000 10050342159337 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306234503/2500000000 : ℝ)^4597 ≤ (671078275633/10000000000000 : ℝ)^3573 := by
    have hnat : (306234503 : ℕ)^4597*10000000000000^3573 ≤ 671078275633^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306234503 2500000000 671078275633 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41543119/80000000 : ℝ), (2928806571/5000000000 : ℝ), (-306234503/2500000000 : ℝ)] ![(10759376610727/25000000000000 : ℝ), (10050342159337/20000000000000 : ℝ), (671078275633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41543119/80000000 : ℝ)|^4597 ≤ (10759376610727/25000000000000 : ℝ)^3573
        have hw : |(41543119/80000000 : ℝ)|=(41543119/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2928806571/5000000000 : ℝ)|^4597 ≤ (10050342159337/20000000000000 : ℝ)^3573
        have hw : |(2928806571/5000000000 : ℝ)|=(2928806571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-306234503/2500000000 : ℝ)|^4597 ≤ (671078275633/10000000000000 : ℝ)^3573
        have hw : |(-306234503/2500000000 : ℝ)|=(306234503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s0_7 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142519281/10000000000 : ℝ)*x 0 + (2695515331/5000000000 : ℝ)*x 1 + (3154022917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142519281/10000000000 : ℝ)^4597 ≤ (4022396734281/12500000000000 : ℝ)^3573 := by
    have hnat : (4142519281 : ℕ)^4597*12500000000000^3573 ≤ 4022396734281^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142519281 10000000000 4022396734281 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695515331/5000000000 : ℝ)^4597 ≤ (2258086539119/5000000000000 : ℝ)^3573 := by
    have hnat : (2695515331 : ℕ)^4597*5000000000000^3573 ≤ 2258086539119^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695515331 5000000000 2258086539119 5000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154022917/10000000000 : ℝ)^4597 ≤ (2832386916569/12500000000000 : ℝ)^3573 := by
    have hnat : (3154022917 : ℕ)^4597*12500000000000^3573 ≤ 2832386916569^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154022917 10000000000 2832386916569 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142519281/10000000000 : ℝ), (2695515331/5000000000 : ℝ), (3154022917/10000000000 : ℝ)] ![(4022396734281/12500000000000 : ℝ), (2258086539119/5000000000000 : ℝ), (2832386916569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142519281/10000000000 : ℝ)|^4597 ≤ (4022396734281/12500000000000 : ℝ)^3573
        have hw : |(4142519281/10000000000 : ℝ)|=(4142519281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695515331/5000000000 : ℝ)|^4597 ≤ (2258086539119/5000000000000 : ℝ)^3573
        have hw : |(2695515331/5000000000 : ℝ)|=(2695515331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154022917/10000000000 : ℝ)|^4597 ≤ (2832386916569/12500000000000 : ℝ)^3573
        have hw : |(3154022917/10000000000 : ℝ)|=(3154022917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1550_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (413/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25001/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4595/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4595 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4595*1^1024 ≤ 0^1024*1^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4595/1024 : ℝ) ≤ (819015155166431813/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4595 ≤ (819015155166431813/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4595*50000000000000000000^1024 ≤ 819015155166431813^1024*5^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 819015155166431813 50000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (819015155166431813/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4595 := by
      have hnat : (1 : ℕ)^1024*1^4595 ≤ 1^4595*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50819015155166431813/50000000000000000000 : ℝ) ≤ (1254534192693159/1250000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (50819015155166431813/50000000000000000000 : ℝ)^1024 ≤ (1254534192693159/1250000000000000 : ℝ)^4595 := by
      have hnat : (50819015155166431813 : ℕ)^1024*1250000000000000^4595 ≤ 1254534192693159^4595*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50819015155166431813 50000000000000000000 1254534192693159 1250000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254534192693159/1250000000000000 : ℝ)) (X := (50819015155166431813/50000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25819015155166431813/25000000000000000000 : ℝ) ≤ (629534192693159/625000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (25819015155166431813/25000000000000000000 : ℝ)^1024 ≤ (629534192693159/625000000000000 : ℝ)^4595 := by
      have hnat : (25819015155166431813 : ℕ)^1024*625000000000000^4595 ≤ 629534192693159^4595*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25819015155166431813 25000000000000000000 629534192693159 625000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629534192693159/625000000000000 : ℝ)) (X := (25819015155166431813/25000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4534192693159/500000000000000 : ℝ)*(0 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4534192693159/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(819015155166431813/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4534192693159/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4595/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4534192693159/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254534192693159/1250000000000000 : ℝ) by norm_num, show 1+(819015155166431813/50000000000000000000 : ℝ)+(0 : ℝ)=(50819015155166431813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(819015155166431813/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4534192693159/500000000000000 : ℝ)*(2/5 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4534192693159/500000000000000 : ℝ)*(2/5 : ℝ)=(629534192693159/625000000000000 : ℝ) by norm_num, show 1+2*(819015155166431813/50000000000000000000 : ℝ)=(25819015155166431813/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4534192693159/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4534192693159/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4534192693159/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4534192693159/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4534192693159/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4534192693159/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-41156557/250000000 : ℝ)*X 0 0+(5884164123/10000000000 : ℝ)*X 0 1+(2435619129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1093952173/2000000000 : ℝ)*X 1 0+(-69103513/312500000 : ℝ)*X 1 1+(974247651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5469760899/10000000000 : ℝ)*X 2 0+(608904777/1250000000 : ℝ)*X 2 1+(-1105656211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2067524413/5000000000 : ℝ)*X 0 0+(48315619/156250000 : ℝ)*X 0 1+(5450730927/10000000000 : ℝ)*X 0 2+(2067524413/5000000000 : ℝ)*X 1 0+(48315619/156250000 : ℝ)*X 1 1+(5450730927/10000000000 : ℝ)*X 1 2+(2067524413/5000000000 : ℝ)*X 2 0+(48315619/156250000 : ℝ)*X 2 1+(5450730927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1649471453/10000000000 : ℝ)*X 0 0+(4896877431/10000000000 : ℝ)*X 0 1+(45762597/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324555659/625000000 : ℝ)*X 1 0+(-7655867/62500000 : ℝ)*X 1 1+(5857612043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41543119/80000000 : ℝ)*X 2 0+(2928806571/5000000000 : ℝ)*X 2 1+(-306234503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4142519281/10000000000 : ℝ)*X 0 0+(2695515331/5000000000 : ℝ)*X 0 1+(3154022917/10000000000 : ℝ)*X 0 2+(4142519281/10000000000 : ℝ)*X 1 0+(2695515331/5000000000 : ℝ)*X 1 1+(3154022917/10000000000 : ℝ)*X 1 2+(4142519281/10000000000 : ℝ)*X 2 0+(2695515331/5000000000 : ℝ)*X 2 1+(3154022917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50735473028767733591907/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39755879/100000000000000 : ℝ)*(base1) + (426917803/50000000000000 : ℝ)*(base19) + (859972311/100000000000000 : ℝ)*(base23) + (110080657/100000000000000 : ℝ)*(upper3) + (27545909/25000000000000 : ℝ)*(upper5) + (352810145076409/50000000000000 : ℝ)*(major0) + (352810145076409/50000000000000 : ℝ)*(major1) + (352810145076409/50000000000000 : ℝ)*(major2) + (493621018122893/50000000000000 : ℝ)*(sp0) + (24681106672893/2500000000000 : ℝ)*(sp1) + (197448852155803/20000000000000 : ℝ)*(sp2) + (423993943891667/100000000000000 : ℝ)*(sp3) + (1562130709/50000000000000 : ℝ)*(sp4) + (670306081/50000000000000 : ℝ)*(sp7) + (423995324259709/100000000000000 : ℝ)*(f.failure) + (493622560375663/50000000000000 : ℝ)*(f.sum) + (3654653788969/12500000000000000000000000000 : ℝ)*base66 + (136064947786031/25000000000000000000000000000 : ℝ)*base67 + (116116333111031/25000000000000000000000000000 : ℝ)*base69 + (90495610013969/25000000000000000000000000000 : ℝ)*base72 + (73258401636031/12500000000000000000000000000 : ℝ)*base73 + (77979214988969/25000000000000000000000000000 : ℝ)*base76 + (9068472861031/25000000000000000000000000000 : ℝ)*base77 + (160421162313969/25000000000000000000000000000 : ℝ)*base80 + (63615327423531/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (15436187/2000000000000000000000 : ℝ)*base89 + (15436187/2000000000000000000000 : ℝ)*base91 + (15436187/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27388143100352326089621/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9149621/2000000000000 : ℝ)*(base19) + (710925903/100000000000000 : ℝ)*(base23) + (41287007/10000000000000 : ℝ)*(base39) + (2180677/20000000000000 : ℝ)*(upper3) + (57453299/20000000000000 : ℝ)*(upper5) + (743946439811473/100000000000000 : ℝ)*(major0) + (743946439811473/100000000000000 : ℝ)*(major1) + (743946026941403/100000000000000 : ℝ)*(major2) + (354274053/25000000000000 : ℝ)*(sp1) + (269308613/25000000000000 : ℝ)*(sp2) + (52043376646139/5000000000000 : ℝ)*(sp4) + (520432829172759/50000000000000 : ℝ)*(sp5) + (65054134852031/6250000000000 : ℝ)*(sp6) + (447024860795043/100000000000000 : ℝ)*(sp7) + (447024860795043/100000000000000 : ℝ)*(f.failure) + (20817358915857/2000000000000 : ℝ)*(f.sum) + (10757977906321/12500000000000000000000000000 : ℝ)*base65 + (89879280337923/50000000000000000000000000000 : ℝ)*base68 + (435303748736793/50000000000000000000000000000 : ℝ)*base70 + (325012410787923/50000000000000000000000000000 : ℝ)*base72 + (1277245768821/12500000000000000000000000000 : ℝ)*base73 + (120535091436793/50000000000000000000000000000 : ℝ)*base76 + (350911624736793/50000000000000000000000000000 : ℝ)*base78 + (210376329686793/50000000000000000000000000000 : ℝ)*base80 + (94121896561793/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3911749/2000000000000000000000 : ℝ)*base89 + (3911749/2000000000000000000000 : ℝ)*base91 + (3911749/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1550_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1550_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1550_s1_0 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894987419/5000000000 : ℝ)*x 0 + (5546498713/10000000000 : ℝ)*x 1 + (5116369741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894987419/5000000000 : ℝ)^4597 ≤ (5466223916759/50000000000000 : ℝ)^3573 := by
    have hnat : (894987419 : ℕ)^4597*50000000000000^3573 ≤ 5466223916759^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894987419 5000000000 5466223916759 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5546498713/10000000000 : ℝ)^4597 ≤ (46844251055839/100000000000000 : ℝ)^3573 := by
    have hnat : (5546498713 : ℕ)^4597*100000000000000^3573 ≤ 46844251055839^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546498713 10000000000 46844251055839 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5116369741/10000000000 : ℝ)^4597 ≤ (10555825274939/25000000000000 : ℝ)^3573 := by
    have hnat : (5116369741 : ℕ)^4597*25000000000000^3573 ≤ 10555825274939^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116369741 10000000000 10555825274939 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894987419/5000000000 : ℝ), (5546498713/10000000000 : ℝ), (5116369741/10000000000 : ℝ)] ![(5466223916759/50000000000000 : ℝ), (46844251055839/100000000000000 : ℝ), (10555825274939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894987419/5000000000 : ℝ)|^4597 ≤ (5466223916759/50000000000000 : ℝ)^3573
        have hw : |(-894987419/5000000000 : ℝ)|=(894987419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5546498713/10000000000 : ℝ)|^4597 ≤ (46844251055839/100000000000000 : ℝ)^3573
        have hw : |(5546498713/10000000000 : ℝ)|=(5546498713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5116369741/10000000000 : ℝ)|^4597 ≤ (10555825274939/25000000000000 : ℝ)^3573
        have hw : |(5116369741/10000000000 : ℝ)|=(5116369741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_1 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379862009/10000000000 : ℝ)*x 0 + (-1007725623/5000000000 : ℝ)*x 1 + (2558184641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379862009/10000000000 : ℝ)^4597 ≤ (9008278043291/20000000000000 : ℝ)^3573 := by
    have hnat : (5379862009 : ℕ)^4597*20000000000000^3573 ≤ 9008278043291^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379862009 10000000000 9008278043291 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007725623/5000000000 : ℝ)^4597 ≤ (12735313536963/100000000000000 : ℝ)^3573 := by
    have hnat : (1007725623 : ℕ)^4597*100000000000000^3573 ≤ 12735313536963^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007725623 5000000000 12735313536963 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558184641/5000000000 : ℝ)^4597 ≤ (42223296226217/100000000000000 : ℝ)^3573 := by
    have hnat : (2558184641 : ℕ)^4597*100000000000000^3573 ≤ 42223296226217^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558184641 5000000000 42223296226217 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379862009/10000000000 : ℝ), (-1007725623/5000000000 : ℝ), (2558184641/5000000000 : ℝ)] ![(9008278043291/20000000000000 : ℝ), (12735313536963/100000000000000 : ℝ), (42223296226217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379862009/10000000000 : ℝ)|^4597 ≤ (9008278043291/20000000000000 : ℝ)^3573
        have hw : |(5379862009/10000000000 : ℝ)|=(5379862009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007725623/5000000000 : ℝ)|^4597 ≤ (12735313536963/100000000000000 : ℝ)^3573
        have hw : |(-1007725623/5000000000 : ℝ)|=(1007725623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2558184641/5000000000 : ℝ)|^4597 ≤ (42223296226217/100000000000000 : ℝ)^3573
        have hw : |(2558184641/5000000000 : ℝ)|=(2558184641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_2 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344965503/2500000000 : ℝ)*x 0 + (639546157/1250000000 : ℝ)*x 1 + (-2015451277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344965503/2500000000 : ℝ)^4597 ≤ (4504139024877/10000000000000 : ℝ)^3573 := by
    have hnat : (1344965503 : ℕ)^4597*10000000000000^3573 ≤ 4504139024877^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344965503 2500000000 4504139024877 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639546157/1250000000 : ℝ)^4597 ≤ (10555823987539/25000000000000 : ℝ)^3573 := by
    have hnat : (639546157 : ℕ)^4597*25000000000000^3573 ≤ 10555823987539^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639546157 1250000000 10555823987539 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015451277/10000000000 : ℝ)^4597 ≤ (12735313788987/100000000000000 : ℝ)^3573 := by
    have hnat : (2015451277 : ℕ)^4597*100000000000000^3573 ≤ 12735313788987^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015451277 10000000000 12735313788987 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344965503/2500000000 : ℝ), (639546157/1250000000 : ℝ), (-2015451277/10000000000 : ℝ)] ![(4504139024877/10000000000000 : ℝ), (10555823987539/25000000000000 : ℝ), (12735313788987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344965503/2500000000 : ℝ)|^4597 ≤ (4504139024877/10000000000000 : ℝ)^3573
        have hw : |(1344965503/2500000000 : ℝ)|=(1344965503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639546157/1250000000 : ℝ)|^4597 ≤ (10555823987539/25000000000000 : ℝ)^3573
        have hw : |(639546157/1250000000 : ℝ)|=(639546157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015451277/10000000000 : ℝ)|^4597 ≤ (12735313788987/100000000000000 : ℝ)^3573
        have hw : |(-2015451277/10000000000 : ℝ)|=(2015451277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_3 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117873509/5000000000 : ℝ)*x 0 + (939806439/2500000000 : ℝ)*x 1 + (476075329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117873509/5000000000 : ℝ)^4597 ≤ (8278476887039/25000000000000 : ℝ)^3573 := by
    have hnat : (2117873509 : ℕ)^4597*25000000000000^3573 ≤ 8278476887039^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117873509 5000000000 8278476887039 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939806439/2500000000 : ℝ)^4597 ≤ (28400383441587/100000000000000 : ℝ)^3573 := by
    have hnat : (939806439 : ℕ)^4597*100000000000000^3573 ≤ 28400383441587^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939806439 2500000000 28400383441587 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476075329/1000000000 : ℝ)^4597 ≤ (3848570899003/10000000000000 : ℝ)^3573 := by
    have hnat : (476075329 : ℕ)^4597*10000000000000^3573 ≤ 3848570899003^3573*1000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476075329 1000000000 3848570899003 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117873509/5000000000 : ℝ), (939806439/2500000000 : ℝ), (476075329/1000000000 : ℝ)] ![(8278476887039/25000000000000 : ℝ), (28400383441587/100000000000000 : ℝ), (3848570899003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117873509/5000000000 : ℝ)|^4597 ≤ (8278476887039/25000000000000 : ℝ)^3573
        have hw : |(2117873509/5000000000 : ℝ)|=(2117873509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(939806439/2500000000 : ℝ)|^4597 ≤ (28400383441587/100000000000000 : ℝ)^3573
        have hw : |(939806439/2500000000 : ℝ)|=(939806439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(476075329/1000000000 : ℝ)|^4597 ≤ (3848570899003/10000000000000 : ℝ)^3573
        have hw : |(476075329/1000000000 : ℝ)|=(476075329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_4 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-895107049/5000000000 : ℝ)*x 0 + (160029057/312500000 : ℝ)*x 1 + (1108373753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895107049/5000000000 : ℝ)^4597 ≤ (2186865594879/20000000000000 : ℝ)^3573 := by
    have hnat : (895107049 : ℕ)^4597*20000000000000^3573 ≤ 2186865594879^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895107049 5000000000 2186865594879 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160029057/312500000 : ℝ)^4597 ≤ (42271725020371/100000000000000 : ℝ)^3573 := by
    have hnat : (160029057 : ℕ)^4597*100000000000000^3573 ≤ 42271725020371^3573*312500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160029057 312500000 42271725020371 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108373753/2000000000 : ℝ)^4597 ≤ (9358789399547/20000000000000 : ℝ)^3573 := by
    have hnat : (1108373753 : ℕ)^4597*20000000000000^3573 ≤ 9358789399547^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108373753 2000000000 9358789399547 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895107049/5000000000 : ℝ), (160029057/312500000 : ℝ), (1108373753/2000000000 : ℝ)] ![(2186865594879/20000000000000 : ℝ), (42271725020371/100000000000000 : ℝ), (9358789399547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895107049/5000000000 : ℝ)|^4597 ≤ (2186865594879/20000000000000 : ℝ)^3573
        have hw : |(-895107049/5000000000 : ℝ)|=(895107049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160029057/312500000 : ℝ)|^4597 ≤ (42271725020371/100000000000000 : ℝ)^3573
        have hw : |(160029057/312500000 : ℝ)|=(160029057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108373753/2000000000 : ℝ)|^4597 ≤ (9358789399547/20000000000000 : ℝ)^3573
        have hw : |(1108373753/2000000000 : ℝ)|=(1108373753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_5 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658259999/1250000000 : ℝ)*x 0 + (-397488379/2500000000 : ℝ)*x 1 + (5541868539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658259999/1250000000 : ℝ)^4597 ≤ (43819503731731/100000000000000 : ℝ)^3573 := by
    have hnat : (658259999 : ℕ)^4597*100000000000000^3573 ≤ 43819503731731^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658259999 1250000000 43819503731731 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397488379/2500000000 : ℝ)^4597 ≤ (9386551708951/100000000000000 : ℝ)^3573 := by
    have hnat : (397488379 : ℕ)^4597*100000000000000^3573 ≤ 9386551708951^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397488379 2500000000 9386551708951 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5541868539/10000000000 : ℝ)^4597 ≤ (9358788908511/20000000000000 : ℝ)^3573 := by
    have hnat : (5541868539 : ℕ)^4597*20000000000000^3573 ≤ 9358788908511^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541868539 10000000000 9358788908511 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658259999/1250000000 : ℝ), (-397488379/2500000000 : ℝ), (5541868539/10000000000 : ℝ)] ![(43819503731731/100000000000000 : ℝ), (9386551708951/100000000000000 : ℝ), (9358788908511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658259999/1250000000 : ℝ)|^4597 ≤ (43819503731731/100000000000000 : ℝ)^3573
        have hw : |(658259999/1250000000 : ℝ)|=(658259999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397488379/2500000000 : ℝ)|^4597 ≤ (9386551708951/100000000000000 : ℝ)^3573
        have hw : |(-397488379/2500000000 : ℝ)|=(397488379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5541868539/10000000000 : ℝ)|^4597 ≤ (9358788908511/20000000000000 : ℝ)^3573
        have hw : |(5541868539/10000000000 : ℝ)|=(5541868539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_6 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266081507/10000000000 : ℝ)*x 0 + (554186829/1000000000 : ℝ)*x 1 + (-1589951737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266081507/10000000000 : ℝ)^4597 ≤ (43819519951107/100000000000000 : ℝ)^3573 := by
    have hnat : (5266081507 : ℕ)^4597*100000000000000^3573 ≤ 43819519951107^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266081507 10000000000 43819519951107 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554186829/1000000000 : ℝ)^4597 ≤ (46793941837511/100000000000000 : ℝ)^3573 := by
    have hnat : (554186829 : ℕ)^4597*100000000000000^3573 ≤ 46793941837511^3573*1000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554186829 1000000000 46793941837511 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1589951737/10000000000 : ℝ)^4597 ≤ (2346634549087/25000000000000 : ℝ)^3573 := by
    have hnat : (1589951737 : ℕ)^4597*25000000000000^3573 ≤ 2346634549087^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589951737 10000000000 2346634549087 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266081507/10000000000 : ℝ), (554186829/1000000000 : ℝ), (-1589951737/10000000000 : ℝ)] ![(43819519951107/100000000000000 : ℝ), (46793941837511/100000000000000 : ℝ), (2346634549087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266081507/10000000000 : ℝ)|^4597 ≤ (43819519951107/100000000000000 : ℝ)^3573
        have hw : |(5266081507/10000000000 : ℝ)|=(5266081507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554186829/1000000000 : ℝ)|^4597 ≤ (46793941837511/100000000000000 : ℝ)^3573
        have hw : |(554186829/1000000000 : ℝ)|=(554186829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1589951737/10000000000 : ℝ)|^4597 ≤ (2346634549087/25000000000000 : ℝ)^3573
        have hw : |(-1589951737/10000000000 : ℝ)|=(1589951737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s1_7 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059075739/2500000000 : ℝ)*x 0 + (4750133063/10000000000 : ℝ)*x 1 + (1885003209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059075739/2500000000 : ℝ)^4597 ≤ (33119499410011/100000000000000 : ℝ)^3573 := by
    have hnat : (1059075739 : ℕ)^4597*100000000000000^3573 ≤ 33119499410011^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059075739 2500000000 33119499410011 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4750133063/10000000000 : ℝ)^4597 ≤ (38375285828353/100000000000000 : ℝ)^3573 := by
    have hnat : (4750133063 : ℕ)^4597*100000000000000^3573 ≤ 38375285828353^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750133063 10000000000 38375285828353 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885003209/5000000000 : ℝ)^4597 ≤ (14252607377467/50000000000000 : ℝ)^3573 := by
    have hnat : (1885003209 : ℕ)^4597*50000000000000^3573 ≤ 14252607377467^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885003209 5000000000 14252607377467 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059075739/2500000000 : ℝ), (4750133063/10000000000 : ℝ), (1885003209/5000000000 : ℝ)] ![(33119499410011/100000000000000 : ℝ), (38375285828353/100000000000000 : ℝ), (14252607377467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059075739/2500000000 : ℝ)|^4597 ≤ (33119499410011/100000000000000 : ℝ)^3573
        have hw : |(1059075739/2500000000 : ℝ)|=(1059075739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4750133063/10000000000 : ℝ)|^4597 ≤ (38375285828353/100000000000000 : ℝ)^3573
        have hw : |(4750133063/10000000000 : ℝ)|=(4750133063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1885003209/5000000000 : ℝ)|^4597 ≤ (14252607377467/50000000000000 : ℝ)^3573
        have hw : |(1885003209/5000000000 : ℝ)|=(1885003209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1550_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4419/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17943/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/12500 : ℝ) ^ (4595/1024 : ℝ) ≤ (22619417850851/100000000000000000000 : ℝ) := by
    have hpowers : (413/12500 : ℝ)^4595 ≤ (22619417850851/100000000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4595*100000000000000000000^1024 ≤ 22619417850851^1024*12500^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 12500 22619417850851 100000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/12500 : ℝ)) (X := (22619417850851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25001/100000 : ℝ) ^ (4595/1024 : ℝ) ≤ (198815998961900973/100000000000000000000 : ℝ) := by
    have hpowers : (25001/100000 : ℝ)^4595 ≤ (198815998961900973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25001 : ℕ)^4595*100000000000000000000^1024 ≤ 198815998961900973^1024*100000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001 100000 198815998961900973 100000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25001/100000 : ℝ)) (X := (198815998961900973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000022619417850851/50000000000000000000 : ℝ) ≤ (10000001008151461/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (50000022619417850851/50000000000000000000 : ℝ)^1024 ≤ (10000001008151461/10000000000000000 : ℝ)^4595 := by
      have hnat : (50000022619417850851 : ℕ)^1024*10000000000000000^4595 ≤ 10000001008151461^4595*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000022619417850851 50000000000000000000 10000001008151461 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001008151461/10000000000000000 : ℝ)) (X := (50000022619417850851/50000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6262427413648734489/6250000000000000000 : ℝ) ≤ (10004427717371623/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (6262427413648734489/6250000000000000000 : ℝ)^1024 ≤ (10004427717371623/10000000000000000 : ℝ)^4595 := by
      have hnat : (6262427413648734489 : ℕ)^1024*10000000000000000^4595 ≤ 10004427717371623^4595*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6262427413648734489 6250000000000000000 10004427717371623 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004427717371623/10000000000000000 : ℝ)) (X := (6262427413648734489/6250000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50198815998961900973/50000000000000000000 : ℝ) ≤ (2001770885318357/2000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (50198815998961900973/50000000000000000000 : ℝ)^1024 ≤ (2001770885318357/2000000000000000 : ℝ)^4595 := by
      have hnat : (50198815998961900973 : ℕ)^1024*2000000000000000^4595 ≤ 2001770885318357^4595*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50198815998961900973 50000000000000000000 2001770885318357 2000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001770885318357/2000000000000000 : ℝ)) (X := (50198815998961900973/50000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22619417850851/100000000000000000000 : ℝ) ≤ ((216940770179335418821/216970000000000000000 : ℝ)+2*(2213354610081/1084850000000000 : ℝ)*(413/12500 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (216940770179335418821/216970000000000000000 : ℝ)+2*(2213354610081/1084850000000000 : ℝ)*(413/12500 : ℝ)=(10000001008151461/10000000000000000 : ℝ) by norm_num, show 1+2*(22619417850851/100000000000000000000 : ℝ)=(50000022619417850851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(198815998961900973/100000000000000000000 : ℝ)+(22619417850851/100000000000000000000 : ℝ) ≤ ((216940770179335418821/216970000000000000000 : ℝ)+(2213354610081/1084850000000000 : ℝ)*((25001/100000 : ℝ)+(413/12500 : ℝ)))^(4595/1024 : ℝ) := by
    rw [show (216940770179335418821/216970000000000000000 : ℝ)+(2213354610081/1084850000000000 : ℝ)*((25001/100000 : ℝ)+(413/12500 : ℝ))=(10004427717371623/10000000000000000 : ℝ) by norm_num, show 1+(198815998961900973/100000000000000000000 : ℝ)+(22619417850851/100000000000000000000 : ℝ)=(6262427413648734489/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(198815998961900973/100000000000000000000 : ℝ) ≤ ((216940770179335418821/216970000000000000000 : ℝ)+2*(2213354610081/1084850000000000 : ℝ)*(25001/100000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (216940770179335418821/216970000000000000000 : ℝ)+2*(2213354610081/1084850000000000 : ℝ)*(25001/100000 : ℝ)=(2001770885318357/2000000000000000 : ℝ) by norm_num, show 1+2*(198815998961900973/100000000000000000000 : ℝ)=(50198815998961900973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (216940770179335418821/216970000000000000000 : ℝ)*(X 1 0+X 2 0)+(2213354610081/1084850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (413/12500 : ℝ)) (hi := (25001/100000 : ℝ)) (c := (216940770179335418821/216970000000000000000 : ℝ)) (alpha := (2213354610081/1084850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (216940770179335418821/216970000000000000000 : ℝ)*(X 0 1+X 2 1)+(2213354610081/1084850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (413/12500 : ℝ)) (hi := (25001/100000 : ℝ)) (c := (216940770179335418821/216970000000000000000 : ℝ)) (alpha := (2213354610081/1084850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (216940770179335418821/216970000000000000000 : ℝ)*(X 0 2+X 1 2)+(2213354610081/1084850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (413/12500 : ℝ)) (hi := (25001/100000 : ℝ)) (c := (216940770179335418821/216970000000000000000 : ℝ)) (alpha := (2213354610081/1084850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894987419/5000000000 : ℝ)*X 0 0+(5546498713/10000000000 : ℝ)*X 0 1+(5116369741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5379862009/10000000000 : ℝ)*X 1 0+(-1007725623/5000000000 : ℝ)*X 1 1+(2558184641/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344965503/2500000000 : ℝ)*X 2 0+(639546157/1250000000 : ℝ)*X 2 1+(-2015451277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117873509/5000000000 : ℝ)*X 0 0+(939806439/2500000000 : ℝ)*X 0 1+(476075329/1000000000 : ℝ)*X 0 2+(2117873509/5000000000 : ℝ)*X 1 0+(939806439/2500000000 : ℝ)*X 1 1+(476075329/1000000000 : ℝ)*X 1 2+(2117873509/5000000000 : ℝ)*X 2 0+(939806439/2500000000 : ℝ)*X 2 1+(476075329/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-895107049/5000000000 : ℝ)*X 0 0+(160029057/312500000 : ℝ)*X 0 1+(1108373753/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658259999/1250000000 : ℝ)*X 1 0+(-397488379/2500000000 : ℝ)*X 1 1+(5541868539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266081507/10000000000 : ℝ)*X 2 0+(554186829/1000000000 : ℝ)*X 2 1+(-1589951737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1059075739/2500000000 : ℝ)*X 0 0+(4750133063/10000000000 : ℝ)*X 0 1+(1885003209/5000000000 : ℝ)*X 0 2+(1059075739/2500000000 : ℝ)*X 1 0+(4750133063/10000000000 : ℝ)*X 1 1+(1885003209/5000000000 : ℝ)*X 1 2+(1059075739/2500000000 : ℝ)*X 2 0+(4750133063/10000000000 : ℝ)*X 2 1+(1885003209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114224818917586995310281/27121250000000000000000000000 : ℝ) := by norm_num
    linear_combination (67177083/100000000000000 : ℝ)*(base1) + (5279907/1000000000000 : ℝ)*(base19) + (264643569/50000000000000 : ℝ)*(base23) + (6946563/12500000000000 : ℝ)*(upper3) + (3909571/10000000000000 : ℝ)*(upper5) + (830840974567283/50000000000000 : ℝ)*(major0) + (830840974567283/50000000000000 : ℝ)*(major1) + (830840974567283/50000000000000 : ℝ)*(major2) + (46497714925113/2000000000000 : ℝ)*(sp0) + (2324886589306403/100000000000000 : ℝ)*(sp1) + (464977317601993/20000000000000 : ℝ)*(sp2) + (249618906727421/25000000000000 : ℝ)*(sp3) + (179777317/12500000000000 : ℝ)*(sp4) + (473248703/50000000000000 : ℝ)*(sp7) + (249619160146043/25000000000000 : ℝ)*(f.failure) + (2324887117297103/100000000000000 : ℝ)*(f.sum) + (19899045992249/13560625000000000000000000000 : ℝ)*base65 + (240074210528643589/834500000000000000000000000000000 : ℝ)*base68 + (1946837383682356411/834500000000000000000000000000000 : ℝ)*base69 + (540979169645856411/834500000000000000000000000000000 : ℝ)*base71 + (89999554447787/27121250000000000000000000000 : ℝ)*base74 + (4965726289400356411/834500000000000000000000000000000 : ℝ)*base75 + (1312283398132643589/834500000000000000000000000000000 : ℝ)*base78 + (1426432728775643589/834500000000000000000000000000000 : ℝ)*base80 + (55780393085637/108485000000000000000000000000 : ℝ)*base81 + (4695251/500000000000000000000 : ℝ)*base90 + (4695251/500000000000000000000 : ℝ)*base92 + (4695251/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69402544530045085663350728439/10848500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (780272959/100000000000000 : ℝ)*(base19) + (1798870939/100000000000000 : ℝ)*(base23) + (6483517/10000000000000 : ℝ)*(upper2) + (185562601/100000000000000 : ℝ)*(upper3) + (356504259/100000000000000 : ℝ)*(upper5) + (1697961271880647/100000000000000 : ℝ)*(major0) + (1697961271880647/100000000000000 : ℝ)*(major1) + (1697961271880647/100000000000000 : ℝ)*(major2) + (638095947/25000000000000 : ℝ)*(sp1) + (6182874063/50000000000000 : ℝ)*(sp2) + (1187823028571711/50000000000000 : ℝ)*(sp4) + (593910681121669/25000000000000 : ℝ)*(sp5) + (2375631892524357/100000000000000 : ℝ)*(sp6) + (1020276273370123/100000000000000 : ℝ)*(sp7) + (1020276273370123/100000000000000 : ℝ)*(f.failure) + (1187823028571711/50000000000000 : ℝ)*(f.sum) + (101864332931853/54242500000000000000000000000 : ℝ)*base66 + (18766039608698604399/1669000000000000000000000000000000 : ℝ)*base67 + (9763839536575604399/1669000000000000000000000000000000 : ℝ)*base69 + (4872150583156395601/1669000000000000000000000000000000 : ℝ)*base72 + (487548184643589/108485000000000000000000000000 : ℝ)*base73 + (3488141883174395601/1669000000000000000000000000000000 : ℝ)*base76 + (4191422634580604399/1669000000000000000000000000000000 : ℝ)*base77 + (13005092127896604399/1669000000000000000000000000000000 : ℝ)*base79 + (79328858795359/108485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (115811/2000000000000000000000 : ℝ)*base90 + (115811/2000000000000000000000 : ℝ)*base92 + (115811/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1550_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17943/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1550_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1550_s2_0 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-113153119/625000000 : ℝ)*x 0 + (2723344623/5000000000 : ℝ)*x 1 + (650357989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113153119/625000000 : ℝ)^4597 ≤ (11093603895797/100000000000000 : ℝ)^3573 := by
    have hnat : (113153119 : ℕ)^4597*100000000000000^3573 ≤ 11093603895797^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113153119 625000000 11093603895797 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723344623/5000000000 : ℝ)^4597 ≤ (5720313401573/12500000000000 : ℝ)^3573 := by
    have hnat : (2723344623 : ℕ)^4597*12500000000000^3573 ≤ 5720313401573^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723344623 5000000000 5720313401573 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650357989/1250000000 : ℝ)^4597 ≤ (43143888874131/100000000000000 : ℝ)^3573 := by
    have hnat : (650357989 : ℕ)^4597*100000000000000^3573 ≤ 43143888874131^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650357989 1250000000 43143888874131 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113153119/625000000 : ℝ), (2723344623/5000000000 : ℝ), (650357989/1250000000 : ℝ)] ![(11093603895797/100000000000000 : ℝ), (5720313401573/12500000000000 : ℝ), (43143888874131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113153119/625000000 : ℝ)|^4597 ≤ (11093603895797/100000000000000 : ℝ)^3573
        have hw : |(-113153119/625000000 : ℝ)|=(113153119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723344623/5000000000 : ℝ)|^4597 ≤ (5720313401573/12500000000000 : ℝ)^3573
        have hw : |(2723344623/5000000000 : ℝ)|=(2723344623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650357989/1250000000 : ℝ)|^4597 ≤ (43143888874131/100000000000000 : ℝ)^3573
        have hw : |(650357989/1250000000 : ℝ)|=(650357989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_1 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070843829/2000000000 : ℝ)*x 0 + (-60490949/312500000 : ℝ)*x 1 + (2601431939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070843829/2000000000 : ℝ)^4597 ≤ (44765363196099/100000000000000 : ℝ)^3573 := by
    have hnat : (1070843829 : ℕ)^4597*100000000000000^3573 ≤ 44765363196099^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070843829 2000000000 44765363196099 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60490949/312500000 : ℝ)^4597 ≤ (12090748270817/100000000000000 : ℝ)^3573 := by
    have hnat : (60490949 : ℕ)^4597*100000000000000^3573 ≤ 12090748270817^3573*312500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60490949 312500000 12090748270817 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601431939/5000000000 : ℝ)^4597 ≤ (4314388851139/10000000000000 : ℝ)^3573 := by
    have hnat : (2601431939 : ℕ)^4597*10000000000000^3573 ≤ 4314388851139^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601431939 5000000000 4314388851139 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070843829/2000000000 : ℝ), (-60490949/312500000 : ℝ), (2601431939/5000000000 : ℝ)] ![(44765363196099/100000000000000 : ℝ), (12090748270817/100000000000000 : ℝ), (4314388851139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070843829/2000000000 : ℝ)|^4597 ≤ (44765363196099/100000000000000 : ℝ)^3573
        have hw : |(1070843829/2000000000 : ℝ)|=(1070843829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-60490949/312500000 : ℝ)|^4597 ≤ (12090748270817/100000000000000 : ℝ)^3573
        have hw : |(-60490949/312500000 : ℝ)|=(60490949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601431939/5000000000 : ℝ)|^4597 ≤ (4314388851139/10000000000000 : ℝ)^3573
        have hw : |(2601431939/5000000000 : ℝ)|=(2601431939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_2 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070843819/2000000000 : ℝ)*x 0 + (5202863929/10000000000 : ℝ)*x 1 + (-60490949/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070843819/2000000000 : ℝ)^4597 ≤ (44765362658253/100000000000000 : ℝ)^3573 := by
    have hnat : (1070843819 : ℕ)^4597*100000000000000^3573 ≤ 44765362658253^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070843819 2000000000 44765362658253 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202863929/10000000000 : ℝ)^4597 ≤ (21571944527751/50000000000000 : ℝ)^3573 := by
    have hnat : (5202863929 : ℕ)^4597*50000000000000^3573 ≤ 21571944527751^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202863929 10000000000 21571944527751 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60490949/312500000 : ℝ)^4597 ≤ (12090748270817/100000000000000 : ℝ)^3573 := by
    have hnat : (60490949 : ℕ)^4597*100000000000000^3573 ≤ 12090748270817^3573*312500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60490949 312500000 12090748270817 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070843819/2000000000 : ℝ), (5202863929/10000000000 : ℝ), (-60490949/312500000 : ℝ)] ![(44765362658253/100000000000000 : ℝ), (21571944527751/50000000000000 : ℝ), (12090748270817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070843819/2000000000 : ℝ)|^4597 ≤ (44765362658253/100000000000000 : ℝ)^3573
        have hw : |(1070843819/2000000000 : ℝ)|=(1070843819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202863929/10000000000 : ℝ)|^4597 ≤ (21571944527751/50000000000000 : ℝ)^3573
        have hw : |(5202863929/10000000000 : ℝ)|=(5202863929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60490949/312500000 : ℝ)|^4597 ≤ (12090748270817/100000000000000 : ℝ)^3573
        have hw : |(-60490949/312500000 : ℝ)|=(60490949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_3 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125270159/5000000000 : ℝ)*x 0 + (1987235267/5000000000 : ℝ)*x 1 + (1135550257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125270159/5000000000 : ℝ)^4597 ≤ (6652555296813/20000000000000 : ℝ)^3573 := by
    have hnat : (2125270159 : ℕ)^4597*20000000000000^3573 ≤ 6652555296813^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125270159 5000000000 6652555296813 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987235267/5000000000 : ℝ)^4597 ≤ (30509505495841/100000000000000 : ℝ)^3573 := by
    have hnat : (1987235267 : ℕ)^4597*100000000000000^3573 ≤ 30509505495841^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987235267 5000000000 30509505495841 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135550257/2500000000 : ℝ)^4597 ≤ (7245543602377/20000000000000 : ℝ)^3573 := by
    have hnat : (1135550257 : ℕ)^4597*20000000000000^3573 ≤ 7245543602377^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135550257 2500000000 7245543602377 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125270159/5000000000 : ℝ), (1987235267/5000000000 : ℝ), (1135550257/2500000000 : ℝ)] ![(6652555296813/20000000000000 : ℝ), (30509505495841/100000000000000 : ℝ), (7245543602377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125270159/5000000000 : ℝ)|^4597 ≤ (6652555296813/20000000000000 : ℝ)^3573
        have hw : |(2125270159/5000000000 : ℝ)|=(2125270159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1987235267/5000000000 : ℝ)|^4597 ≤ (30509505495841/100000000000000 : ℝ)^3573
        have hw : |(1987235267/5000000000 : ℝ)|=(1987235267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135550257/2500000000 : ℝ)|^4597 ≤ (7245543602377/20000000000000 : ℝ)^3573
        have hw : |(1135550257/2500000000 : ℝ)|=(1135550257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_4 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905246621/5000000000 : ℝ)*x 0 + (5204337507/10000000000 : ℝ)*x 1 + (5445203143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905246621/5000000000 : ℝ)^4597 ≤ (443757822353/4000000000000 : ℝ)^3573 := by
    have hnat : (905246621 : ℕ)^4597*4000000000000^3573 ≤ 443757822353^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905246621 5000000000 443757822353 4000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204337507/10000000000 : ℝ)^4597 ≤ (1348737846923/3125000000000 : ℝ)^3573 := by
    have hnat : (5204337507 : ℕ)^4597*3125000000000^3573 ≤ 1348737846923^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204337507 10000000000 1348737846923 3125000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445203143/10000000000 : ℝ)^4597 ≤ (4574644332599/10000000000000 : ℝ)^3573 := by
    have hnat : (5445203143 : ℕ)^4597*10000000000000^3573 ≤ 4574644332599^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445203143 10000000000 4574644332599 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905246621/5000000000 : ℝ), (5204337507/10000000000 : ℝ), (5445203143/10000000000 : ℝ)] ![(443757822353/4000000000000 : ℝ), (1348737846923/3125000000000 : ℝ), (4574644332599/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905246621/5000000000 : ℝ)|^4597 ≤ (443757822353/4000000000000 : ℝ)^3573
        have hw : |(-905246621/5000000000 : ℝ)|=(905246621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204337507/10000000000 : ℝ)|^4597 ≤ (1348737846923/3125000000000 : ℝ)^3573
        have hw : |(5204337507/10000000000 : ℝ)|=(5204337507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445203143/10000000000 : ℝ)|^4597 ≤ (4574644332599/10000000000000 : ℝ)^3573
        have hw : |(5445203143/10000000000 : ℝ)|=(5445203143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_5 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644931157/5000000000 : ℝ)*x 0 + (-211671349/1250000000 : ℝ)*x 1 + (2722601431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644931157/5000000000 : ℝ)^4597 ≤ (44074278494799/100000000000000 : ℝ)^3573 := by
    have hnat : (2644931157 : ℕ)^4597*100000000000000^3573 ≤ 44074278494799^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644931157 5000000000 44074278494799 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211671349/1250000000 : ℝ)^4597 ≤ (10179281203219/100000000000000 : ℝ)^3573 := by
    have hnat : (211671349 : ℕ)^4597*100000000000000^3573 ≤ 10179281203219^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211671349 1250000000 10179281203219 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722601431/5000000000 : ℝ)^4597 ≤ (45746440288667/100000000000000 : ℝ)^3573 := by
    have hnat : (2722601431 : ℕ)^4597*100000000000000^3573 ≤ 45746440288667^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722601431 5000000000 45746440288667 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644931157/5000000000 : ℝ), (-211671349/1250000000 : ℝ), (2722601431/5000000000 : ℝ)] ![(44074278494799/100000000000000 : ℝ), (10179281203219/100000000000000 : ℝ), (45746440288667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644931157/5000000000 : ℝ)|^4597 ≤ (44074278494799/100000000000000 : ℝ)^3573
        have hw : |(2644931157/5000000000 : ℝ)|=(2644931157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211671349/1250000000 : ℝ)|^4597 ≤ (10179281203219/100000000000000 : ℝ)^3573
        have hw : |(-211671349/1250000000 : ℝ)|=(211671349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722601431/5000000000 : ℝ)|^4597 ≤ (45746440288667/100000000000000 : ℝ)^3573
        have hw : |(2722601431/5000000000 : ℝ)|=(2722601431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_6 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289861473/10000000000 : ℝ)*x 0 + (5445203423/10000000000 : ℝ)*x 1 + (-846685587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289861473/10000000000 : ℝ)^4597 ≤ (22037134739769/50000000000000 : ℝ)^3573 := by
    have hnat : (5289861473 : ℕ)^4597*50000000000000^3573 ≤ 22037134739769^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289861473 10000000000 22037134739769 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445203423/10000000000 : ℝ)^4597 ≤ (9149289270501/20000000000000 : ℝ)^3573 := by
    have hnat : (5445203423 : ℕ)^4597*20000000000000^3573 ≤ 9149289270501^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445203423 10000000000 9149289270501 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846685587/5000000000 : ℝ)^4597 ≤ (10179284157623/100000000000000 : ℝ)^3573 := by
    have hnat : (846685587 : ℕ)^4597*100000000000000^3573 ≤ 10179284157623^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846685587 5000000000 10179284157623 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289861473/10000000000 : ℝ), (5445203423/10000000000 : ℝ), (-846685587/5000000000 : ℝ)] ![(22037134739769/50000000000000 : ℝ), (9149289270501/20000000000000 : ℝ), (10179284157623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289861473/10000000000 : ℝ)|^4597 ≤ (22037134739769/50000000000000 : ℝ)^3573
        have hw : |(5289861473/10000000000 : ℝ)|=(5289861473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445203423/10000000000 : ℝ)|^4597 ≤ (9149289270501/20000000000000 : ℝ)^3573
        have hw : |(5445203423/10000000000 : ℝ)|=(5445203423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846685587/5000000000 : ℝ)|^4597 ≤ (10179284157623/100000000000000 : ℝ)^3573
        have hw : |(-846685587/5000000000 : ℝ)|=(846685587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s2_7 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250640153/10000000000 : ℝ)*x 0 + (4538769653/10000000000 : ℝ)*x 1 + (795586633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250640153/10000000000 : ℝ)^4597 ≤ (16631890827739/50000000000000 : ℝ)^3573 := by
    have hnat : (4250640153 : ℕ)^4597*50000000000000^3573 ≤ 16631890827739^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250640153 10000000000 16631890827739 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538769653/10000000000 : ℝ)^4597 ≤ (18096255171419/50000000000000 : ℝ)^3573 := by
    have hnat : (4538769653 : ℕ)^4597*50000000000000^3573 ≤ 18096255171419^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538769653 10000000000 18096255171419 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795586633/2000000000 : ℝ)^4597 ≤ (305437079911/1000000000000 : ℝ)^3573 := by
    have hnat : (795586633 : ℕ)^4597*1000000000000^3573 ≤ 305437079911^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795586633 2000000000 305437079911 1000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250640153/10000000000 : ℝ), (4538769653/10000000000 : ℝ), (795586633/2000000000 : ℝ)] ![(16631890827739/50000000000000 : ℝ), (18096255171419/50000000000000 : ℝ), (305437079911/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250640153/10000000000 : ℝ)|^4597 ≤ (16631890827739/50000000000000 : ℝ)^3573
        have hw : |(4250640153/10000000000 : ℝ)|=(4250640153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538769653/10000000000 : ℝ)|^4597 ≤ (18096255171419/50000000000000 : ℝ)^3573
        have hw : |(4538769653/10000000000 : ℝ)|=(4538769653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795586633/2000000000 : ℝ)|^4597 ≤ (305437079911/1000000000000 : ℝ)^3573
        have hw : |(795586633/2000000000 : ℝ)|=(795586633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1550_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5351/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3967/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4419/50000 : ℝ) ^ (4595/1024 : ℝ) ≤ (1870550135074373/100000000000000000000 : ℝ) := by
    have hpowers : (4419/50000 : ℝ)^4595 ≤ (1870550135074373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4419 : ℕ)^4595*100000000000000000000^1024 ≤ 1870550135074373^1024*50000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4419 50000 1870550135074373 100000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4419/50000 : ℝ)) (X := (1870550135074373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17943/100000 : ℝ) ^ (4595/1024 : ℝ) ≤ (11218629388230527/25000000000000000000 : ℝ) := by
    have hpowers : (17943/100000 : ℝ)^4595 ≤ (11218629388230527/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17943 : ℕ)^4595*25000000000000000000^1024 ≤ 11218629388230527^1024*100000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17943 100000 11218629388230527 25000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17943/100000 : ℝ)) (X := (11218629388230527/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001870550135074373/50000000000000000000 : ℝ) ≤ (10000083369553611/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (50001870550135074373/50000000000000000000 : ℝ)^1024 ≤ (10000083369553611/10000000000000000 : ℝ)^4595 := by
      have hnat : (50001870550135074373 : ℕ)^1024*10000000000000000^4595 ≤ 10000083369553611^4595*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001870550135074373 50000000000000000000 10000083369553611 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083369553611/10000000000000000 : ℝ)) (X := (50001870550135074373/50000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046745067687996481/100000000000000000000 : ℝ) ≤ (10001041528992251/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (100046745067687996481/100000000000000000000 : ℝ)^1024 ≤ (10001041528992251/10000000000000000 : ℝ)^4595 := by
      have hnat : (100046745067687996481 : ℕ)^1024*10000000000000000^4595 ≤ 10001041528992251^4595*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046745067687996481 100000000000000000000 10001041528992251 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001041528992251/10000000000000000 : ℝ)) (X := (100046745067687996481/100000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511218629388230527/12500000000000000000 : ℝ) ≤ (10001999688430891/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (12511218629388230527/12500000000000000000 : ℝ)^1024 ≤ (10001999688430891/10000000000000000 : ℝ)^4595 := by
      have hnat : (12511218629388230527 : ℕ)^1024*10000000000000000^4595 ≤ 10001999688430891^4595*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511218629388230527 12500000000000000000 10001999688430891 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001999688430891/10000000000000000 : ℝ)) (X := (12511218629388230527/12500000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1870550135074373/100000000000000000000 : ℝ) ≤ ((6068921510236548501/6070000000000000000 : ℝ)+2*(11976992983/11381250000000 : ℝ)*(4419/50000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (6068921510236548501/6070000000000000000 : ℝ)+2*(11976992983/11381250000000 : ℝ)*(4419/50000 : ℝ)=(10000083369553611/10000000000000000 : ℝ) by norm_num, show 1+2*(1870550135074373/100000000000000000000 : ℝ)=(50001870550135074373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11218629388230527/25000000000000000000 : ℝ)+(1870550135074373/100000000000000000000 : ℝ) ≤ ((6068921510236548501/6070000000000000000 : ℝ)+(11976992983/11381250000000 : ℝ)*((17943/100000 : ℝ)+(4419/50000 : ℝ)))^(4595/1024 : ℝ) := by
    rw [show (6068921510236548501/6070000000000000000 : ℝ)+(11976992983/11381250000000 : ℝ)*((17943/100000 : ℝ)+(4419/50000 : ℝ))=(10001041528992251/10000000000000000 : ℝ) by norm_num, show 1+(11218629388230527/25000000000000000000 : ℝ)+(1870550135074373/100000000000000000000 : ℝ)=(100046745067687996481/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11218629388230527/25000000000000000000 : ℝ) ≤ ((6068921510236548501/6070000000000000000 : ℝ)+2*(11976992983/11381250000000 : ℝ)*(17943/100000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (6068921510236548501/6070000000000000000 : ℝ)+2*(11976992983/11381250000000 : ℝ)*(17943/100000 : ℝ)=(10001999688430891/10000000000000000 : ℝ) by norm_num, show 1+2*(11218629388230527/25000000000000000000 : ℝ)=(12511218629388230527/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6068921510236548501/6070000000000000000 : ℝ)*(X 1 0+X 2 0)+(11976992983/11381250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (17943/100000 : ℝ)) (c := (6068921510236548501/6070000000000000000 : ℝ)) (alpha := (11976992983/11381250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6068921510236548501/6070000000000000000 : ℝ)*(X 0 1+X 2 1)+(11976992983/11381250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (17943/100000 : ℝ)) (c := (6068921510236548501/6070000000000000000 : ℝ)) (alpha := (11976992983/11381250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6068921510236548501/6070000000000000000 : ℝ)*(X 0 2+X 1 2)+(11976992983/11381250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (17943/100000 : ℝ)) (c := (6068921510236548501/6070000000000000000 : ℝ)) (alpha := (11976992983/11381250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-113153119/625000000 : ℝ)*X 0 0+(2723344623/5000000000 : ℝ)*X 0 1+(650357989/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070843829/2000000000 : ℝ)*X 1 0+(-60490949/312500000 : ℝ)*X 1 1+(2601431939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070843819/2000000000 : ℝ)*X 2 0+(5202863929/10000000000 : ℝ)*X 2 1+(-60490949/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125270159/5000000000 : ℝ)*X 0 0+(1987235267/5000000000 : ℝ)*X 0 1+(1135550257/2500000000 : ℝ)*X 0 2+(2125270159/5000000000 : ℝ)*X 1 0+(1987235267/5000000000 : ℝ)*X 1 1+(1135550257/2500000000 : ℝ)*X 1 2+(2125270159/5000000000 : ℝ)*X 2 0+(1987235267/5000000000 : ℝ)*X 2 1+(1135550257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-905246621/5000000000 : ℝ)*X 0 0+(5204337507/10000000000 : ℝ)*X 0 1+(5445203143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644931157/5000000000 : ℝ)*X 1 0+(-211671349/1250000000 : ℝ)*X 1 1+(2722601431/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289861473/10000000000 : ℝ)*X 2 0+(5445203423/10000000000 : ℝ)*X 2 1+(-846685587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250640153/10000000000 : ℝ)*X 0 0+(4538769653/10000000000 : ℝ)*X 0 1+(795586633/2000000000 : ℝ)*X 0 2+(4250640153/10000000000 : ℝ)*X 1 0+(4538769653/10000000000 : ℝ)*X 1 1+(795586633/2000000000 : ℝ)*X 1 2+(4250640153/10000000000 : ℝ)*X 2 0+(4538769653/10000000000 : ℝ)*X 2 1+(795586633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249973712578610428953249837/75875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360707473/100000000000000 : ℝ)*(base19) + (327364157/100000000000000 : ℝ)*(base23) + (1914443/12500000000000 : ℝ)*(lower2) + (2153879/100000000000000 : ℝ)*(upper3) + (4492337/25000000000000 : ℝ)*(lower4) + (1465678060501779/50000000000000 : ℝ)*(major0) + (1465678060501779/50000000000000 : ℝ)*(major1) + (1465678060501779/50000000000000 : ℝ)*(major2) + (1025325808217409/25000000000000 : ℝ)*(sp0) + (4101309348123653/100000000000000 : ℝ)*(sp1) + (410130938146697/10000000000000 : ℝ)*(sp2) + (1761400806314631/100000000000000 : ℝ)*(sp3) + (6475961491/100000000000000 : ℝ)*(sp4) + (1617043137/100000000000000 : ℝ)*(sp7) + (220175302919721/12500000000000 : ℝ)*(f.failure) + (2050654854415563/50000000000000 : ℝ)*(f.sum) + (16736626801553/3035000000000000000000000000 : ℝ)*base65 + (2025209113327316721/303500000000000000000000000000000 : ℝ)*base68 + (2452367065312316721/303500000000000000000000000000000 : ℝ)*base70 + (166674508363316721/303500000000000000000000000000000 : ℝ)*base72 + (1208485558523/3035000000000000000000000000 : ℝ)*base73 + (991307166323816721/303500000000000000000000000000000 : ℝ)*base76 + (693488358009183279/303500000000000000000000000000000 : ℝ)*base77 + (4361505901506816721/303500000000000000000000000000000 : ℝ)*base80 + (14996295705453/3035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (228303/250000000000000000000 : ℝ)*base89 + (228303/250000000000000000000 : ℝ)*base91 + (228303/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272807980530865993005077013/30350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40771179/4000000000000 : ℝ)*(base19) + (121010627/25000000000000 : ℝ)*(base23) + (61878567/50000000000000 : ℝ)*(upper2) + (41815517/25000000000000 : ℝ)*(lower3) + (296737796532171/10000000000000 : ℝ)*(major0) + (296737796532171/10000000000000 : ℝ)*(major1) + (296737796532171/10000000000000 : ℝ)*(major2) + (4384387229/50000000000000 : ℝ)*(sp0) + (15007118999/50000000000000 : ℝ)*(sp1) + (21043448481/100000000000000 : ℝ)*(sp2) + (1037924880135749/25000000000000 : ℝ)*(sp4) + (2075838627899991/50000000000000 : ℝ)*(sp5) + (830337352365293/20000000000000 : ℝ)*(sp6) + (891523670850799/50000000000000 : ℝ)*(sp7) + (891523670850799/50000000000000 : ℝ)*(f.failure) + (2075854144658727/50000000000000 : ℝ)*(f.sum) + (838422125491/303500000000000000000000000 : ℝ)*base65 + (211812031335874329/60700000000000000000000000000000 : ℝ)*base68 + (244903348002125671/60700000000000000000000000000000 : ℝ)*base69 + (294459902008474329/60700000000000000000000000000000 : ℝ)*base72 + (274999775799/60700000000000000000000000 : ℝ)*base73 + (282809620260674329/60700000000000000000000000000000 : ℝ)*base76 + (206164708764125671/60700000000000000000000000000000 : ℝ)*base77 + (481180536908674329/60700000000000000000000000000000 : ℝ)*base80 + (91098632079/18968750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4259943/1000000000000000000000 : ℝ)*base90 + (4259943/1000000000000000000000 : ℝ)*base92 + (4259943/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1550_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3967/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1550_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1550_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3967/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1550_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1550_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1550_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3967/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
