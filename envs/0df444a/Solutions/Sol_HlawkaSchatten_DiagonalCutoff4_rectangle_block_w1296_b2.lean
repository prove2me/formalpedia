-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:42.643583+00:00
-- url     : https://prove2.me/submissions/e120068b-592f-4210-b8f7-2e196133e9b3

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
theorem support_rectangle_w1296_s6_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042189759/5000000000 : ℝ)*x 0 + (1353778833/2500000000 : ℝ)*x 1 + (1310762831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042189759/5000000000 : ℝ)^133 ≤ (6341282097551/50000000000000 : ℝ)^101 := by
    have hnat : (1042189759 : ℕ)^133*50000000000000^101 ≤ 6341282097551^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042189759 5000000000 6341282097551 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353778833/2500000000 : ℝ)^133 ≤ (44586788629007/100000000000000 : ℝ)^101 := by
    have hnat : (1353778833 : ℕ)^133*100000000000000^101 ≤ 44586788629007^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353778833 2500000000 44586788629007 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310762831/2500000000 : ℝ)^133 ≤ (42730647159811/100000000000000 : ℝ)^101 := by
    have hnat : (1310762831 : ℕ)^133*100000000000000^101 ≤ 42730647159811^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310762831 2500000000 42730647159811 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042189759/5000000000 : ℝ), (1353778833/2500000000 : ℝ), (1310762831/2500000000 : ℝ)] ![(6341282097551/50000000000000 : ℝ), (44586788629007/100000000000000 : ℝ), (42730647159811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042189759/5000000000 : ℝ)|^133 ≤ (6341282097551/50000000000000 : ℝ)^101
        have hw : |(-1042189759/5000000000 : ℝ)|=(1042189759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353778833/2500000000 : ℝ)|^133 ≤ (44586788629007/100000000000000 : ℝ)^101
        have hw : |(1353778833/2500000000 : ℝ)|=(1353778833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310762831/2500000000 : ℝ)|^133 ≤ (42730647159811/100000000000000 : ℝ)^101
        have hw : |(1310762831/2500000000 : ℝ)|=(1310762831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5349748277/10000000000 : ℝ)*x 0 + (-543021681/2500000000 : ℝ)*x 1 + (209722053/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349748277/10000000000 : ℝ)^133 ≤ (43879406497593/100000000000000 : ℝ)^101 := by
    have hnat : (5349748277 : ℕ)^133*100000000000000^101 ≤ 43879406497593^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349748277 10000000000 43879406497593 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543021681/2500000000 : ℝ)^133 ≤ (1338994632127/10000000000000 : ℝ)^101 := by
    have hnat : (543021681 : ℕ)^133*10000000000000^101 ≤ 1338994632127^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543021681 2500000000 1338994632127 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209722053/400000000 : ℝ)^133 ≤ (42730647170543/100000000000000 : ℝ)^101 := by
    have hnat : (209722053 : ℕ)^133*100000000000000^101 ≤ 42730647170543^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209722053 400000000 42730647170543 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349748277/10000000000 : ℝ), (-543021681/2500000000 : ℝ), (209722053/400000000 : ℝ)] ![(43879406497593/100000000000000 : ℝ), (1338994632127/10000000000000 : ℝ), (42730647170543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349748277/10000000000 : ℝ)|^133 ≤ (43879406497593/100000000000000 : ℝ)^101
        have hw : |(5349748277/10000000000 : ℝ)|=(5349748277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543021681/2500000000 : ℝ)|^133 ≤ (1338994632127/10000000000000 : ℝ)^101
        have hw : |(-543021681/2500000000 : ℝ)|=(543021681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209722053/400000000 : ℝ)|^133 ≤ (42730647170543/100000000000000 : ℝ)^101
        have hw : |(209722053/400000000 : ℝ)|=(209722053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2674874139/5000000000 : ℝ)*x 0 + (5243051323/10000000000 : ℝ)*x 1 + (-86883469/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674874139/5000000000 : ℝ)^133 ≤ (21939703254197/50000000000000 : ℝ)^101 := by
    have hnat : (2674874139 : ℕ)^133*50000000000000^101 ≤ 21939703254197^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674874139 5000000000 21939703254197 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243051323/10000000000 : ℝ)^133 ≤ (42730647149079/100000000000000 : ℝ)^101 := by
    have hnat : (5243051323 : ℕ)^133*100000000000000^101 ≤ 42730647149079^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243051323 10000000000 42730647149079 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86883469/400000000 : ℝ)^133 ≤ (3347486582347/25000000000000 : ℝ)^101 := by
    have hnat : (86883469 : ℕ)^133*25000000000000^101 ≤ 3347486582347^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86883469 400000000 3347486582347 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674874139/5000000000 : ℝ), (5243051323/10000000000 : ℝ), (-86883469/400000000 : ℝ)] ![(21939703254197/50000000000000 : ℝ), (42730647149079/100000000000000 : ℝ), (3347486582347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674874139/5000000000 : ℝ)|^133 ≤ (21939703254197/50000000000000 : ℝ)^101
        have hw : |(2674874139/5000000000 : ℝ)|=(2674874139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243051323/10000000000 : ℝ)|^133 ≤ (42730647149079/100000000000000 : ℝ)^101
        have hw : |(5243051323/10000000000 : ℝ)|=(5243051323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86883469/400000000 : ℝ)|^133 ≤ (3347486582347/25000000000000 : ℝ)^101
        have hw : |(-86883469/400000000 : ℝ)|=(86883469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (433878843/1000000000 : ℝ)*x 0 + (520643771/1250000000 : ℝ)*x 1 + (4519323093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433878843/1000000000 : ℝ)^133 ≤ (16651191701011/50000000000000 : ℝ)^101 := by
    have hnat : (433878843 : ℕ)^133*50000000000000^101 ≤ 16651191701011^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433878843 1000000000 16651191701011 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520643771/1250000000 : ℝ)^133 ≤ (7889647783761/25000000000000 : ℝ)^101 := by
    have hnat : (520643771 : ℕ)^133*25000000000000^101 ≤ 7889647783761^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520643771 1250000000 7889647783761 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519323093/10000000000 : ℝ)^133 ≤ (8784756363921/25000000000000 : ℝ)^101 := by
    have hnat : (4519323093 : ℕ)^133*25000000000000^101 ≤ 8784756363921^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519323093 10000000000 8784756363921 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433878843/1000000000 : ℝ), (520643771/1250000000 : ℝ), (4519323093/10000000000 : ℝ)] ![(16651191701011/50000000000000 : ℝ), (7889647783761/25000000000000 : ℝ), (8784756363921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433878843/1000000000 : ℝ)|^133 ≤ (16651191701011/50000000000000 : ℝ)^101
        have hw : |(433878843/1000000000 : ℝ)|=(433878843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520643771/1250000000 : ℝ)|^133 ≤ (7889647783761/25000000000000 : ℝ)^101
        have hw : |(520643771/1250000000 : ℝ)|=(520643771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519323093/10000000000 : ℝ)|^133 ≤ (8784756363921/25000000000000 : ℝ)^101
        have hw : |(4519323093/10000000000 : ℝ)|=(4519323093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-208439219/1000000000 : ℝ)*x 0 + (5120767/9765625 : ℝ)*x 1 + (84601533/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208439219/1000000000 : ℝ)^133 ≤ (2536533145569/20000000000000 : ℝ)^101 := by
    have hnat : (208439219 : ℕ)^133*20000000000000^101 ≤ 2536533145569^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208439219 1000000000 2536533145569 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5120767/9765625 : ℝ)^133 ≤ (42737237706911/100000000000000 : ℝ)^101 := by
    have hnat : (5120767 : ℕ)^133*100000000000000^101 ≤ 42737237706911^101*9765625^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120767 9765625 42737237706911 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84601533/156250000 : ℝ)^133 ≤ (11145024138123/25000000000000 : ℝ)^101 := by
    have hnat : (84601533 : ℕ)^133*25000000000000^101 ≤ 11145024138123^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84601533 156250000 11145024138123 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208439219/1000000000 : ℝ), (5120767/9765625 : ℝ), (84601533/156250000 : ℝ)] ![(2536533145569/20000000000000 : ℝ), (42737237706911/100000000000000 : ℝ), (11145024138123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208439219/1000000000 : ℝ)|^133 ≤ (2536533145569/20000000000000 : ℝ)^101
        have hw : |(-208439219/1000000000 : ℝ)|=(208439219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5120767/9765625 : ℝ)|^133 ≤ (42737237706911/100000000000000 : ℝ)^101
        have hw : |(5120767/9765625 : ℝ)|=(5120767/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84601533/156250000 : ℝ)|^133 ≤ (11145024138123/25000000000000 : ℝ)^101
        have hw : |(84601533/156250000 : ℝ)|=(84601533/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652836623/5000000000 : ℝ)*x 0 + (-500159977/2500000000 : ℝ)*x 1 + (5414498103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652836623/5000000000 : ℝ)^133 ≤ (21701990737397/50000000000000 : ℝ)^101 := by
    have hnat : (2652836623 : ℕ)^133*50000000000000^101 ≤ 21701990737397^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652836623 5000000000 21701990737397 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500159977/2500000000 : ℝ)^133 ≤ (6007961031981/50000000000000 : ℝ)^101 := by
    have hnat : (500159977 : ℕ)^133*50000000000000^101 ≤ 6007961031981^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500159977 2500000000 6007961031981 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414498103/10000000000 : ℝ)^133 ≤ (44580096454913/100000000000000 : ℝ)^101 := by
    have hnat : (5414498103 : ℕ)^133*100000000000000^101 ≤ 44580096454913^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414498103 10000000000 44580096454913 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652836623/5000000000 : ℝ), (-500159977/2500000000 : ℝ), (5414498103/10000000000 : ℝ)] ![(21701990737397/50000000000000 : ℝ), (6007961031981/50000000000000 : ℝ), (44580096454913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652836623/5000000000 : ℝ)|^133 ≤ (21701990737397/50000000000000 : ℝ)^101
        have hw : |(2652836623/5000000000 : ℝ)|=(2652836623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-500159977/2500000000 : ℝ)|^133 ≤ (6007961031981/50000000000000 : ℝ)^101
        have hw : |(-500159977/2500000000 : ℝ)|=(500159977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414498103/10000000000 : ℝ)|^133 ≤ (44580096454913/100000000000000 : ℝ)^101
        have hw : |(5414498103/10000000000 : ℝ)|=(5414498103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305673213/10000000000 : ℝ)*x 0 + (8663197/16000000 : ℝ)*x 1 + (-2000639921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305673213/10000000000 : ℝ)^133 ≤ (43403981119299/100000000000000 : ℝ)^101 := by
    have hnat : (5305673213 : ℕ)^133*100000000000000^101 ≤ 43403981119299^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305673213 10000000000 43403981119299 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8663197/16000000 : ℝ)^133 ≤ (44580096693439/100000000000000 : ℝ)^101 := by
    have hnat : (8663197 : ℕ)^133*100000000000000^101 ≤ 44580096693439^101*16000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8663197 16000000 44580096693439 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000639921/10000000000 : ℝ)^133 ≤ (12015922166779/100000000000000 : ℝ)^101 := by
    have hnat : (2000639921 : ℕ)^133*100000000000000^101 ≤ 12015922166779^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000639921 10000000000 12015922166779 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305673213/10000000000 : ℝ), (8663197/16000000 : ℝ), (-2000639921/10000000000 : ℝ)] ![(43403981119299/100000000000000 : ℝ), (44580096693439/100000000000000 : ℝ), (12015922166779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305673213/10000000000 : ℝ)|^133 ≤ (43403981119299/100000000000000 : ℝ)^101
        have hw : |(5305673213/10000000000 : ℝ)|=(5305673213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8663197/16000000 : ℝ)|^133 ≤ (44580096693439/100000000000000 : ℝ)^101
        have hw : |(8663197/16000000 : ℝ)|=(8663197/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2000639921/10000000000 : ℝ)|^133 ≤ (12015922166779/100000000000000 : ℝ)^101
        have hw : |(-2000639921/10000000000 : ℝ)|=(2000639921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s6_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4338814581/10000000000 : ℝ)*x 0 + (903611823/2000000000 : ℝ)*x 1 + (1041605161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338814581/10000000000 : ℝ)^133 ≤ (6660529543893/20000000000000 : ℝ)^101 := by
    have hnat : (4338814581 : ℕ)^133*20000000000000^101 ≤ 6660529543893^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338814581 10000000000 6660529543893 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903611823/2000000000 : ℝ)^133 ≤ (35126084484791/100000000000000 : ℝ)^101 := by
    have hnat : (903611823 : ℕ)^133*100000000000000^101 ≤ 35126084484791^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903611823 2000000000 35126084484791 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041605161/2500000000 : ℝ)^133 ≤ (246650529607/781250000000 : ℝ)^101 := by
    have hnat : (1041605161 : ℕ)^133*781250000000^101 ≤ 246650529607^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041605161 2500000000 246650529607 781250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338814581/10000000000 : ℝ), (903611823/2000000000 : ℝ), (1041605161/2500000000 : ℝ)] ![(6660529543893/20000000000000 : ℝ), (35126084484791/100000000000000 : ℝ), (246650529607/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338814581/10000000000 : ℝ)|^133 ≤ (6660529543893/20000000000000 : ℝ)^101
        have hw : |(4338814581/10000000000 : ℝ)|=(4338814581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903611823/2000000000 : ℝ)|^133 ≤ (35126084484791/100000000000000 : ℝ)^101
        have hw : |(903611823/2000000000 : ℝ)|=(903611823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041605161/2500000000 : ℝ)|^133 ≤ (246650529607/781250000000 : ℝ)^101
        have hw : |(1041605161/2500000000 : ℝ)|=(1041605161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2759/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (441/4000 : ℝ) ^ (4255/1024 : ℝ) ≤ (5245552403269749/50000000000000000000 : ℝ) := by
    have hpowers : (441/4000 : ℝ)^4255 ≤ (5245552403269749/50000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4255*50000000000000000000^1024 ≤ 5245552403269749^1024*4000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 4000 5245552403269749 50000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/4000 : ℝ)) (X := (5245552403269749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (34564075374435261/100000000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^4255 ≤ (34564075374435261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14689 : ℕ)^4255*100000000000000000000^1024 ≤ 34564075374435261^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 34564075374435261 100000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (34564075374435261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005245552403269749/25000000000000000000 : ℝ) ≤ (5000252456771149/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (25005245552403269749/25000000000000000000 : ℝ)^1024 ≤ (5000252456771149/5000000000000000 : ℝ)^4255 := by
      have hnat : (25005245552403269749 : ℕ)^1024*5000000000000000^4255 ≤ 5000252456771149^4255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005245552403269749 25000000000000000000 5000252456771149 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000252456771149/5000000000000000 : ℝ)) (X := (25005245552403269749/25000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045055180180974759/100000000000000000000 : ℝ) ≤ (10001084103746487/10000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (100045055180180974759/100000000000000000000 : ℝ)^1024 ≤ (10001084103746487/10000000000000000 : ℝ)^4255 := by
      have hnat : (100045055180180974759 : ℕ)^1024*10000000000000000^4255 ≤ 10001084103746487^4255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045055180180974759 100000000000000000000 10001084103746487 10000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084103746487/10000000000000000 : ℝ)) (X := (100045055180180974759/100000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034564075374435261/50000000000000000000 : ℝ) ≤ (2500415823487669/2500000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (50034564075374435261/50000000000000000000 : ℝ)^1024 ≤ (2500415823487669/2500000000000000 : ℝ)^4255 := by
      have hnat : (50034564075374435261 : ℕ)^1024*2500000000000000^4255 ≤ 2500415823487669^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034564075374435261 50000000000000000000 2500415823487669 2500000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500415823487669/2500000000000000 : ℝ)) (X := (50034564075374435261/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5245552403269749/50000000000000000000 : ℝ) ≤ ((18314539429608306211/18320000000000000000 : ℝ)+2*(579190204189/366400000000000 : ℝ)*(441/4000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (18314539429608306211/18320000000000000000 : ℝ)+2*(579190204189/366400000000000 : ℝ)*(441/4000 : ℝ)=(5000252456771149/5000000000000000 : ℝ) by norm_num, show 1+2*(5245552403269749/50000000000000000000 : ℝ)=(25005245552403269749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34564075374435261/100000000000000000000 : ℝ)+(5245552403269749/50000000000000000000 : ℝ) ≤ ((18314539429608306211/18320000000000000000 : ℝ)+(579190204189/366400000000000 : ℝ)*((14689/100000 : ℝ)+(441/4000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (18314539429608306211/18320000000000000000 : ℝ)+(579190204189/366400000000000 : ℝ)*((14689/100000 : ℝ)+(441/4000 : ℝ))=(10001084103746487/10000000000000000 : ℝ) by norm_num, show 1+(34564075374435261/100000000000000000000 : ℝ)+(5245552403269749/50000000000000000000 : ℝ)=(100045055180180974759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34564075374435261/100000000000000000000 : ℝ) ≤ ((18314539429608306211/18320000000000000000 : ℝ)+2*(579190204189/366400000000000 : ℝ)*(14689/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (18314539429608306211/18320000000000000000 : ℝ)+2*(579190204189/366400000000000 : ℝ)*(14689/100000 : ℝ)=(2500415823487669/2500000000000000 : ℝ) by norm_num, show 1+2*(34564075374435261/100000000000000000000 : ℝ)=(50034564075374435261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18314539429608306211/18320000000000000000 : ℝ)*(X 1 0+X 2 0)+(579190204189/366400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (18314539429608306211/18320000000000000000 : ℝ)) (alpha := (579190204189/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18314539429608306211/18320000000000000000 : ℝ)*(X 0 1+X 2 1)+(579190204189/366400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (18314539429608306211/18320000000000000000 : ℝ)) (alpha := (579190204189/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18314539429608306211/18320000000000000000 : ℝ)*(X 0 2+X 1 2)+(579190204189/366400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (18314539429608306211/18320000000000000000 : ℝ)) (alpha := (579190204189/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1042189759/5000000000 : ℝ)*X 0 0+(1353778833/2500000000 : ℝ)*X 0 1+(1310762831/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349748277/10000000000 : ℝ)*X 1 0+(-543021681/2500000000 : ℝ)*X 1 1+(209722053/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674874139/5000000000 : ℝ)*X 2 0+(5243051323/10000000000 : ℝ)*X 2 1+(-86883469/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433878843/1000000000 : ℝ)*X 0 0+(520643771/1250000000 : ℝ)*X 0 1+(4519323093/10000000000 : ℝ)*X 0 2+(433878843/1000000000 : ℝ)*X 1 0+(520643771/1250000000 : ℝ)*X 1 1+(4519323093/10000000000 : ℝ)*X 1 2+(433878843/1000000000 : ℝ)*X 2 0+(520643771/1250000000 : ℝ)*X 2 1+(4519323093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208439219/1000000000 : ℝ)*X 0 0+(5120767/9765625 : ℝ)*X 0 1+(84601533/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652836623/5000000000 : ℝ)*X 1 0+(-500159977/2500000000 : ℝ)*X 1 1+(5414498103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305673213/10000000000 : ℝ)*X 2 0+(8663197/16000000 : ℝ)*X 2 1+(-2000639921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338814581/10000000000 : ℝ)*X 0 0+(903611823/2000000000 : ℝ)*X 0 1+(1041605161/2500000000 : ℝ)*X 0 2+(4338814581/10000000000 : ℝ)*X 1 0+(903611823/2000000000 : ℝ)*X 1 1+(1041605161/2500000000 : ℝ)*X 1 2+(4338814581/10000000000 : ℝ)*X 2 0+(903611823/2000000000 : ℝ)*X 2 1+(1041605161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24126605615542065271785399/5725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50397753/6250000000000 : ℝ)*(base19) + (751688923/100000000000000 : ℝ)*(base23) + (29830997/100000000000000 : ℝ)*(lower2) + (107193691/100000000000000 : ℝ)*(upper3) + (64597463/100000000000000 : ℝ)*(upper5) + (53970747486503/1250000000000 : ℝ)*(major0) + (53970747486503/1250000000000 : ℝ)*(major1) + (53970747486503/1250000000000 : ℝ)*(major2) + (726475953383803/12500000000000 : ℝ)*(sp0) + (5811822975615711/100000000000000 : ℝ)*(sp1) + (1452955757572709/25000000000000 : ℝ)*(sp2) + (1411743570641033/50000000000000 : ℝ)*(sp3) + (3230981867/20000000000000 : ℝ)*(sp4) + (1706820701/20000000000000 : ℝ)*(sp7) + (705873918846393/25000000000000 : ℝ)*(f.failure) + (5811823781979759/100000000000000 : ℝ)*(f.sum) + (3102138611/2862500000000000000000000 : ℝ)*base65 + (215166152624979867/22900000000000000000000000000000 : ℝ)*base68 + (53703167949679867/22900000000000000000000000000000 : ℝ)*base70 + (18738497095879867/22900000000000000000000000000000 : ℝ)*base72 + (3727997089/3578125000000000000000000 : ℝ)*base73 + (231029702951220133/22900000000000000000000000000000 : ℝ)*base75 + (220116527652779867/22900000000000000000000000000000 : ℝ)*base78 + (128206873806979867/22900000000000000000000000000000 : ℝ)*base80 + (343792881397/45800000000000000000000000 : ℝ)*base81 + (6923077/500000000000000000000 : ℝ)*base89 + (6923077/500000000000000000000 : ℝ)*base91 + (6923077/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1317313371376664800264906761/458000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256164027/50000000000000 : ℝ)*(base19) + (559903377/100000000000000 : ℝ)*(base23) + (13430883/25000000000000 : ℝ)*(upper3) + (495671/1250000000000 : ℝ)*(lower4) + (46770047/100000000000000 : ℝ)*(upper5) + (2174377122869983/50000000000000 : ℝ)*(major0) + (2174377122869983/50000000000000 : ℝ)*(major1) + (2174377122869983/50000000000000 : ℝ)*(major2) + (10261859937/100000000000000 : ℝ)*(sp1) + (11374810159/100000000000000 : ℝ)*(sp2) + (2926839390013621/50000000000000 : ℝ)*(sp4) + (5853668005839251/100000000000000 : ℝ)*(sp5) + (2926833422656853/50000000000000 : ℝ)*(sp6) + (710957403894587/25000000000000 : ℝ)*(sp7) + (710957403894587/25000000000000 : ℝ)*(f.failure) + (2926839390013621/50000000000000 : ℝ)*(f.sum) + (43277078733507/9160000000000000000000000000 : ℝ)*base65 + (872932607247714413/916000000000000000000000000000000 : ℝ)*base67 + (7111262249887714413/916000000000000000000000000000000 : ℝ)*base69 + (2299636749315714413/916000000000000000000000000000000 : ℝ)*base71 + (12151771433053/9160000000000000000000000000 : ℝ)*base74 + (3878118241096285587/916000000000000000000000000000000 : ℝ)*base76 + (86228407744285587/916000000000000000000000000000000 : ℝ)*base78 + (10931027673411714413/916000000000000000000000000000000 : ℝ)*base79 + (7261090677973/9160000000000000000000000000 : ℝ)*base82 + (2949857/500000000000000000000 : ℝ)*base90 + (2949857/500000000000000000000 : ℝ)*base92 + (2949857/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1296_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_s7_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-208439253/1000000000 : ℝ)*x 0 + (135375297/250000000 : ℝ)*x 1 + (41945169/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208439253/1000000000 : ℝ)^133 ≤ (6341334226027/50000000000000 : ℝ)^101 := by
    have hnat : (208439253 : ℕ)^133*50000000000000^101 ≤ 6341334226027^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208439253 1000000000 6341334226027 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135375297/250000000 : ℝ)^133 ≤ (44585666955851/100000000000000 : ℝ)^101 := by
    have hnat : (135375297 : ℕ)^133*100000000000000^101 ≤ 44585666955851^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135375297 250000000 44585666955851 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41945169/80000000 : ℝ)^133 ≤ (333841129521/781250000000 : ℝ)^101 := by
    have hnat : (41945169 : ℕ)^133*781250000000^101 ≤ 333841129521^101*80000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41945169 80000000 333841129521 781250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208439253/1000000000 : ℝ), (135375297/250000000 : ℝ), (41945169/80000000 : ℝ)] ![(6341334226027/50000000000000 : ℝ), (44585666955851/100000000000000 : ℝ), (333841129521/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208439253/1000000000 : ℝ)|^133 ≤ (6341334226027/50000000000000 : ℝ)^101
        have hw : |(-208439253/1000000000 : ℝ)|=(208439253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135375297/250000000 : ℝ)|^133 ≤ (44585666955851/100000000000000 : ℝ)^101
        have hw : |(135375297/250000000 : ℝ)|=(135375297/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41945169/80000000 : ℝ)|^133 ≤ (333841129521/781250000000 : ℝ)^101
        have hw : |(41945169/80000000 : ℝ)|=(41945169/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5349720873/10000000000 : ℝ)*x 0 + (-542999037/2500000000 : ℝ)*x 1 + (2621573707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349720873/10000000000 : ℝ)^133 ≤ (10969777627881/25000000000000 : ℝ)^101 := by
    have hnat : (5349720873 : ℕ)^133*25000000000000^101 ≤ 10969777627881^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349720873 10000000000 10969777627881 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542999037/2500000000 : ℝ)^133 ≤ (13389211059119/100000000000000 : ℝ)^101 := by
    have hnat : (542999037 : ℕ)^133*100000000000000^101 ≤ 13389211059119^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542999037 2500000000 13389211059119 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621573707/5000000000 : ℝ)^133 ≤ (21365839206237/50000000000000 : ℝ)^101 := by
    have hnat : (2621573707 : ℕ)^133*50000000000000^101 ≤ 21365839206237^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621573707 5000000000 21365839206237 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349720873/10000000000 : ℝ), (-542999037/2500000000 : ℝ), (2621573707/5000000000 : ℝ)] ![(10969777627881/25000000000000 : ℝ), (13389211059119/100000000000000 : ℝ), (21365839206237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349720873/10000000000 : ℝ)|^133 ≤ (10969777627881/25000000000000 : ℝ)^101
        have hw : |(5349720873/10000000000 : ℝ)|=(5349720873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542999037/2500000000 : ℝ)|^133 ≤ (13389211059119/100000000000000 : ℝ)^101
        have hw : |(-542999037/2500000000 : ℝ)|=(542999037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621573707/5000000000 : ℝ)|^133 ≤ (21365839206237/50000000000000 : ℝ)^101
        have hw : |(2621573707/5000000000 : ℝ)|=(2621573707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2674860629/5000000000 : ℝ)*x 0 + (41945169/80000000 : ℝ)*x 1 + (-108599867/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674860629/5000000000 : ℝ)^133 ≤ (21939557334921/50000000000000 : ℝ)^101 := by
    have hnat : (2674860629 : ℕ)^133*50000000000000^101 ≤ 21939557334921^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674860629 5000000000 21939557334921 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41945169/80000000 : ℝ)^133 ≤ (333841129521/781250000000 : ℝ)^101 := by
    have hnat : (41945169 : ℕ)^133*781250000000^101 ≤ 333841129521^101*80000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41945169 80000000 333841129521 781250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108599867/500000000 : ℝ)^133 ≤ (13389220735267/100000000000000 : ℝ)^101 := by
    have hnat : (108599867 : ℕ)^133*100000000000000^101 ≤ 13389220735267^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108599867 500000000 13389220735267 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674860629/5000000000 : ℝ), (41945169/80000000 : ℝ), (-108599867/500000000 : ℝ)] ![(21939557334921/50000000000000 : ℝ), (333841129521/781250000000 : ℝ), (13389220735267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674860629/5000000000 : ℝ)|^133 ≤ (21939557334921/50000000000000 : ℝ)^101
        have hw : |(2674860629/5000000000 : ℝ)|=(2674860629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41945169/80000000 : ℝ)|^133 ≤ (333841129521/781250000000 : ℝ)^101
        have hw : |(41945169/80000000 : ℝ)|=(41945169/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108599867/500000000 : ℝ)|^133 ≤ (13389220735267/100000000000000 : ℝ)^101
        have hw : |(-108599867/500000000 : ℝ)|=(108599867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4338795033/10000000000 : ℝ)*x 0 + (416535441/1000000000 : ℝ)*x 1 + (2259558771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338795033/10000000000 : ℝ)^133 ≤ (832561253521/2500000000000 : ℝ)^101 := by
    have hnat : (4338795033 : ℕ)^133*2500000000000^101 ≤ 832561253521^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338795033 10000000000 832561253521 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416535441/1000000000 : ℝ)^133 ≤ (3156062895419/10000000000000 : ℝ)^101 := by
    have hnat : (416535441 : ℕ)^133*10000000000000^101 ≤ 3156062895419^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416535441 1000000000 3156062895419 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259558771/5000000000 : ℝ)^133 ≤ (17568460443621/50000000000000 : ℝ)^101 := by
    have hnat : (2259558771 : ℕ)^133*50000000000000^101 ≤ 17568460443621^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259558771 5000000000 17568460443621 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338795033/10000000000 : ℝ), (416535441/1000000000 : ℝ), (2259558771/5000000000 : ℝ)] ![(832561253521/2500000000000 : ℝ), (3156062895419/10000000000000 : ℝ), (17568460443621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338795033/10000000000 : ℝ)|^133 ≤ (832561253521/2500000000000 : ℝ)^101
        have hw : |(4338795033/10000000000 : ℝ)|=(4338795033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416535441/1000000000 : ℝ)|^133 ≤ (3156062895419/10000000000000 : ℝ)^101
        have hw : |(416535441/1000000000 : ℝ)|=(416535441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259558771/5000000000 : ℝ)|^133 ≤ (17568460443621/50000000000000 : ℝ)^101
        have hw : |(2259558771/5000000000 : ℝ)|=(2259558771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084404737/10000000000 : ℝ)*x 0 + (1310939819/2500000000 : ℝ)*x 1 + (5414395919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084404737/10000000000 : ℝ)^133 ≤ (3170691564809/25000000000000 : ℝ)^101 := by
    have hnat : (2084404737 : ℕ)^133*25000000000000^101 ≤ 3170691564809^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084404737 10000000000 3170691564809 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310939819/2500000000 : ℝ)^133 ≤ (21369122575021/50000000000000 : ℝ)^101 := by
    have hnat : (1310939819 : ℕ)^133*50000000000000^101 ≤ 21369122575021^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310939819 2500000000 21369122575021 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414395919/10000000000 : ℝ)^133 ≤ (8915797713991/20000000000000 : ℝ)^101 := by
    have hnat : (5414395919 : ℕ)^133*20000000000000^101 ≤ 8915797713991^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414395919 10000000000 8915797713991 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084404737/10000000000 : ℝ), (1310939819/2500000000 : ℝ), (5414395919/10000000000 : ℝ)] ![(3170691564809/25000000000000 : ℝ), (21369122575021/50000000000000 : ℝ), (8915797713991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084404737/10000000000 : ℝ)|^133 ≤ (3170691564809/25000000000000 : ℝ)^101
        have hw : |(-2084404737/10000000000 : ℝ)|=(2084404737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310939819/2500000000 : ℝ)|^133 ≤ (21369122575021/50000000000000 : ℝ)^101
        have hw : |(1310939819/2500000000 : ℝ)|=(1310939819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414395919/10000000000 : ℝ)|^133 ≤ (8915797713991/20000000000000 : ℝ)^101
        have hw : |(5414395919/10000000000 : ℝ)|=(5414395919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652848749/5000000000 : ℝ)*x 0 + (-2000746853/10000000000 : ℝ)*x 1 + (676799499/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652848749/5000000000 : ℝ)^133 ≤ (21702121365679/50000000000000 : ℝ)^101 := by
    have hnat : (2652848749 : ℕ)^133*50000000000000^101 ≤ 21702121365679^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652848749 5000000000 21702121365679 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000746853/10000000000 : ℝ)^133 ≤ (3004191973257/25000000000000 : ℝ)^101 := by
    have hnat : (2000746853 : ℕ)^133*25000000000000^101 ≤ 3004191973257^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000746853 10000000000 3004191973257 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676799499/1250000000 : ℝ)^133 ≤ (44578989361423/100000000000000 : ℝ)^101 := by
    have hnat : (676799499 : ℕ)^133*100000000000000^101 ≤ 44578989361423^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676799499 1250000000 44578989361423 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652848749/5000000000 : ℝ), (-2000746853/10000000000 : ℝ), (676799499/1250000000 : ℝ)] ![(21702121365679/50000000000000 : ℝ), (3004191973257/25000000000000 : ℝ), (44578989361423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652848749/5000000000 : ℝ)|^133 ≤ (21702121365679/50000000000000 : ℝ)^101
        have hw : |(2652848749/5000000000 : ℝ)|=(2652848749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000746853/10000000000 : ℝ)|^133 ≤ (3004191973257/25000000000000 : ℝ)^101
        have hw : |(-2000746853/10000000000 : ℝ)|=(2000746853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676799499/1250000000 : ℝ)|^133 ≤ (44578989361423/100000000000000 : ℝ)^101
        have hw : |(676799499/1250000000 : ℝ)|=(676799499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1061139489/2000000000 : ℝ)*x 0 + (5414396037/10000000000 : ℝ)*x 1 + (-125046679/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061139489/2000000000 : ℝ)^133 ≤ (43404242160411/100000000000000 : ℝ)^101 := by
    have hnat : (1061139489 : ℕ)^133*100000000000000^101 ≤ 43404242160411^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061139489 2000000000 43404242160411 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414396037/10000000000 : ℝ)^133 ≤ (22289494924657/50000000000000 : ℝ)^101 := by
    have hnat : (5414396037 : ℕ)^133*50000000000000^101 ≤ 22289494924657^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414396037 10000000000 22289494924657 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125046679/625000000 : ℝ)^133 ≤ (12016767980027/100000000000000 : ℝ)^101 := by
    have hnat : (125046679 : ℕ)^133*100000000000000^101 ≤ 12016767980027^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125046679 625000000 12016767980027 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061139489/2000000000 : ℝ), (5414396037/10000000000 : ℝ), (-125046679/625000000 : ℝ)] ![(43404242160411/100000000000000 : ℝ), (22289494924657/50000000000000 : ℝ), (12016767980027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061139489/2000000000 : ℝ)|^133 ≤ (43404242160411/100000000000000 : ℝ)^101
        have hw : |(1061139489/2000000000 : ℝ)|=(1061139489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414396037/10000000000 : ℝ)|^133 ≤ (22289494924657/50000000000000 : ℝ)^101
        have hw : |(5414396037/10000000000 : ℝ)|=(5414396037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125046679/625000000 : ℝ)|^133 ≤ (12016767980027/100000000000000 : ℝ)^101
        have hw : |(-125046679/625000000 : ℝ)|=(125046679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s7_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (433882147/1000000000 : ℝ)*x 0 + (451785643/1000000000 : ℝ)*x 1 + (2083310809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433882147/1000000000 : ℝ)^133 ≤ (33302717349119/100000000000000 : ℝ)^101 := by
    have hnat : (433882147 : ℕ)^133*100000000000000^101 ≤ 33302717349119^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433882147 1000000000 33302717349119 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451785643/1000000000 : ℝ)^133 ≤ (8781002361019/25000000000000 : ℝ)^101 := by
    have hnat : (451785643 : ℕ)^133*25000000000000^101 ≤ 8781002361019^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451785643 1000000000 8781002361019 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083310809/5000000000 : ℝ)^133 ≤ (7893318298993/25000000000000 : ℝ)^101 := by
    have hnat : (2083310809 : ℕ)^133*25000000000000^101 ≤ 7893318298993^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083310809 5000000000 7893318298993 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433882147/1000000000 : ℝ), (451785643/1000000000 : ℝ), (2083310809/5000000000 : ℝ)] ![(33302717349119/100000000000000 : ℝ), (8781002361019/25000000000000 : ℝ), (7893318298993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433882147/1000000000 : ℝ)|^133 ≤ (33302717349119/100000000000000 : ℝ)^101
        have hw : |(433882147/1000000000 : ℝ)|=(433882147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451785643/1000000000 : ℝ)|^133 ≤ (8781002361019/25000000000000 : ℝ)^101
        have hw : |(451785643/1000000000 : ℝ)|=(451785643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083310809/5000000000 : ℝ)|^133 ≤ (7893318298993/25000000000000 : ℝ)^101
        have hw : |(2083310809/5000000000 : ℝ)|=(2083310809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5519/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (587/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2759/25000 : ℝ) ^ (4255/1024 : ℝ) ≤ (421386715060247/4000000000000000000 : ℝ) := by
    have hpowers : (2759/25000 : ℝ)^4255 ≤ (421386715060247/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2759 : ℕ)^4255*4000000000000000000^1024 ≤ 421386715060247^1024*25000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 25000 421386715060247 4000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/25000 : ℝ)) (X := (421386715060247/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14677/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (6889379058241567/20000000000000000000 : ℝ) := by
    have hpowers : (14677/100000 : ℝ)^4255 ≤ (6889379058241567/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14677 : ℕ)^4255*20000000000000000000^1024 ≤ 6889379058241567^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14677 100000 6889379058241567 20000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14677/100000 : ℝ)) (X := (6889379058241567/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000421386715060247/2000000000000000000 : ℝ) ≤ (2500126752492071/2500000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (2000421386715060247/2000000000000000000 : ℝ)^1024 ≤ (2500126752492071/2500000000000000 : ℝ)^4255 := by
      have hnat : (2000421386715060247 : ℕ)^1024*2500000000000000^4255 ≤ 2500126752492071^4255*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000421386715060247 2000000000000000000 2500126752492071 2500000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126752492071/2500000000000000 : ℝ)) (X := (2000421386715060247/2000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004498156316771401/10000000000000000000 : ℝ) ≤ (5000541166349597/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (10004498156316771401/10000000000000000000 : ℝ)^1024 ≤ (5000541166349597/5000000000000000 : ℝ)^4255 := by
      have hnat : (10004498156316771401 : ℕ)^1024*5000000000000000^4255 ≤ 5000541166349597^4255*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004498156316771401 10000000000000000000 5000541166349597 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000541166349597/5000000000000000 : ℝ)) (X := (10004498156316771401/10000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006889379058241567/10000000000000000000 : ℝ) ≤ (1250207206928763/1250000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (10006889379058241567/10000000000000000000 : ℝ)^1024 ≤ (1250207206928763/1250000000000000 : ℝ)^4255 := by
      have hnat : (10006889379058241567 : ℕ)^1024*1250000000000000^4255 ≤ 1250207206928763^4255*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006889379058241567 10000000000000000000 1250207206928763 1250000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250207206928763/1250000000000000 : ℝ)) (X := (10006889379058241567/10000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(421386715060247/4000000000000000000 : ℝ) ≤ ((9099786874994469131/9102500000000000000 : ℝ)+2*(57532273091/36410000000000 : ℝ)*(2759/25000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (9099786874994469131/9102500000000000000 : ℝ)+2*(57532273091/36410000000000 : ℝ)*(2759/25000 : ℝ)=(2500126752492071/2500000000000000 : ℝ) by norm_num, show 1+2*(421386715060247/4000000000000000000 : ℝ)=(2000421386715060247/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6889379058241567/20000000000000000000 : ℝ)+(421386715060247/4000000000000000000 : ℝ) ≤ ((9099786874994469131/9102500000000000000 : ℝ)+(57532273091/36410000000000 : ℝ)*((14677/100000 : ℝ)+(2759/25000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (9099786874994469131/9102500000000000000 : ℝ)+(57532273091/36410000000000 : ℝ)*((14677/100000 : ℝ)+(2759/25000 : ℝ))=(5000541166349597/5000000000000000 : ℝ) by norm_num, show 1+(6889379058241567/20000000000000000000 : ℝ)+(421386715060247/4000000000000000000 : ℝ)=(10004498156316771401/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6889379058241567/20000000000000000000 : ℝ) ≤ ((9099786874994469131/9102500000000000000 : ℝ)+2*(57532273091/36410000000000 : ℝ)*(14677/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (9099786874994469131/9102500000000000000 : ℝ)+2*(57532273091/36410000000000 : ℝ)*(14677/100000 : ℝ)=(1250207206928763/1250000000000000 : ℝ) by norm_num, show 1+2*(6889379058241567/20000000000000000000 : ℝ)=(10006889379058241567/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9099786874994469131/9102500000000000000 : ℝ)*(X 1 0+X 2 0)+(57532273091/36410000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9099786874994469131/9102500000000000000 : ℝ)) (alpha := (57532273091/36410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9099786874994469131/9102500000000000000 : ℝ)*(X 0 1+X 2 1)+(57532273091/36410000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9099786874994469131/9102500000000000000 : ℝ)) (alpha := (57532273091/36410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9099786874994469131/9102500000000000000 : ℝ)*(X 0 2+X 1 2)+(57532273091/36410000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (9099786874994469131/9102500000000000000 : ℝ)) (alpha := (57532273091/36410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208439253/1000000000 : ℝ)*X 0 0+(135375297/250000000 : ℝ)*X 0 1+(41945169/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349720873/10000000000 : ℝ)*X 1 0+(-542999037/2500000000 : ℝ)*X 1 1+(2621573707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674860629/5000000000 : ℝ)*X 2 0+(41945169/80000000 : ℝ)*X 2 1+(-108599867/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338795033/10000000000 : ℝ)*X 0 0+(416535441/1000000000 : ℝ)*X 0 1+(2259558771/5000000000 : ℝ)*X 0 2+(4338795033/10000000000 : ℝ)*X 1 0+(416535441/1000000000 : ℝ)*X 1 1+(2259558771/5000000000 : ℝ)*X 1 2+(4338795033/10000000000 : ℝ)*X 2 0+(416535441/1000000000 : ℝ)*X 2 1+(2259558771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2084404737/10000000000 : ℝ)*X 0 0+(1310939819/2500000000 : ℝ)*X 0 1+(5414395919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652848749/5000000000 : ℝ)*X 1 0+(-2000746853/10000000000 : ℝ)*X 1 1+(676799499/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061139489/2000000000 : ℝ)*X 2 0+(5414396037/10000000000 : ℝ)*X 2 1+(-125046679/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433882147/1000000000 : ℝ)*X 0 0+(451785643/1000000000 : ℝ)*X 0 1+(2083310809/5000000000 : ℝ)*X 0 2+(433882147/1000000000 : ℝ)*X 1 0+(451785643/1000000000 : ℝ)*X 1 1+(2083310809/5000000000 : ℝ)*X 1 2+(433882147/1000000000 : ℝ)*X 2 0+(451785643/1000000000 : ℝ)*X 2 1+(2083310809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197478310732423785103304289/28445312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (288501427/100000000000000 : ℝ)*(base15) + (107252259/100000000000000 : ℝ)*(upper2) + (22395009/10000000000000 : ℝ)*(upper3) + (463529/1000000000000 : ℝ)*(upper4) + (1080664342998579/25000000000000 : ℝ)*(major0) + (1080664342998579/25000000000000 : ℝ)*(major1) + (1080664342998579/25000000000000 : ℝ)*(major2) + (5818528832306987/100000000000000 : ℝ)*(sp0) + (727318803712903/12500000000000 : ℝ)*(sp1) + (290925823742033/5000000000000 : ℝ)*(sp2) + (706689049765339/25000000000000 : ℝ)*(sp3) + (341967151/1562500000000 : ℝ)*(sp4) + (34243363991/100000000000000 : ℝ)*(sp6) + (7595309783/100000000000000 : ℝ)*(sp7) + (2826763794371139/100000000000000 : ℝ)*(f.failure) + (5818550718204651/100000000000000 : ℝ)*(f.sum) + (867262142377/227562500000000000000000000 : ℝ)*base65 + (25345060912489849/227562500000000000000000000000000 : ℝ)*base67 + (2060611047269802349/227562500000000000000000000000000 : ℝ)*base69 + (1602442200170239849/227562500000000000000000000000000 : ℝ)*base71 + (1504980157647/1820500000000000000000000000 : ℝ)*base73 + (2426906082148239849/227562500000000000000000000000000 : ℝ)*base75 + (1695683949517552349/227562500000000000000000000000000 : ℝ)*base77 + (268576790203947651/227562500000000000000000000000000 : ℝ)*base80 + (1717882543621/364100000000000000000000000 : ℝ)*base81 + (17134329/2000000000000000000000 : ℝ)*base90 + (17134329/2000000000000000000000 : ℝ)*base92 + (17134329/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54672192340447796691272643/9102500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211675081/100000000000000 : ℝ)*(base19) + (60888831/10000000000000 : ℝ)*(base23) + (142270763/100000000000000 : ℝ)*(lower1) + (52880119/25000000000000 : ℝ)*(lower4) + (6608993/25000000000000 : ℝ)*(upper5) + (87074864613917/2000000000000 : ℝ)*(major0) + (87074864613917/2000000000000 : ℝ)*(major1) + (87074864613917/2000000000000 : ℝ)*(major2) + (141551983/100000000000000 : ℝ)*(sp0) + (3440062407/50000000000000 : ℝ)*(sp2) + (2930197000595381/50000000000000 : ℝ)*(sp4) + (366274620691729/6250000000000 : ℝ)*(sp5) + (5860386653729621/100000000000000 : ℝ)*(sp6) + (2847092118439511/100000000000000 : ℝ)*(sp7) + (2847092118439511/100000000000000 : ℝ)*(f.failure) + (1172078828548549/20000000000000 : ℝ)*(f.sum) + (4900438261463/1820500000000000000000000000 : ℝ)*base66 + (41289302201563873/18205000000000000000000000000000 : ℝ)*base68 + (205680322381708873/18205000000000000000000000000000 : ℝ)*base70 + (176378298802363873/18205000000000000000000000000000 : ℝ)*base72 + (14466824005021/1820500000000000000000000000 : ℝ)*base73 + (26845080251383873/18205000000000000000000000000000 : ℝ)*base76 + (97297775617788873/18205000000000000000000000000000 : ℝ)*base78 + (157560839183438873/18205000000000000000000000000000 : ℝ)*base80 + (2992301425523/1820500000000000000000000000 : ℝ)*base81 + (13687179/2000000000000000000000 : ℝ)*base89 + (13687179/2000000000000000000000 : ℝ)*base91 + (13687179/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1296_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (587/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_box_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913381663/10000000000 : ℝ)*x 0 + (1347962127/2500000000 : ℝ)*x 1 + (2695924307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913381663/10000000000 : ℝ)^133 ≤ (11330618105107/100000000000000 : ℝ)^101 := by
    have hnat : (1913381663 : ℕ)^133*100000000000000^101 ≤ 11330618105107^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913381663 10000000000 11330618105107 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347962127/2500000000 : ℝ)^133 ≤ (22167345181503/50000000000000 : ℝ)^101 := by
    have hnat : (1347962127 : ℕ)^133*50000000000000^101 ≤ 22167345181503^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347962127 2500000000 22167345181503 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695924307/5000000000 : ℝ)^133 ≤ (44334691510743/100000000000000 : ℝ)^101 := by
    have hnat : (2695924307 : ℕ)^133*100000000000000^101 ≤ 44334691510743^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695924307 5000000000 44334691510743 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913381663/10000000000 : ℝ), (1347962127/2500000000 : ℝ), (2695924307/5000000000 : ℝ)] ![(11330618105107/100000000000000 : ℝ), (22167345181503/50000000000000 : ℝ), (44334691510743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913381663/10000000000 : ℝ)|^133 ≤ (11330618105107/100000000000000 : ℝ)^101
        have hw : |(-1913381663/10000000000 : ℝ)|=(1913381663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347962127/2500000000 : ℝ)|^133 ≤ (22167345181503/50000000000000 : ℝ)^101
        have hw : |(1347962127/2500000000 : ℝ)|=(1347962127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695924307/5000000000 : ℝ)|^133 ≤ (44334691510743/100000000000000 : ℝ)^101
        have hw : |(2695924307/5000000000 : ℝ)|=(2695924307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5284440313/10000000000 : ℝ)*x 0 + (-2060291047/10000000000 : ℝ)*x 1 + (336990551/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284440313/10000000000 : ℝ)^133 ≤ (21587696676887/50000000000000 : ℝ)^101 := by
    have hnat : (5284440313 : ℕ)^133*50000000000000^101 ≤ 21587696676887^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284440313 10000000000 21587696676887 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060291047/10000000000 : ℝ)^133 ≤ (12489912936661/100000000000000 : ℝ)^101 := by
    have hnat : (2060291047 : ℕ)^133*100000000000000^101 ≤ 12489912936661^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060291047 10000000000 12489912936661 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336990551/625000000 : ℝ)^133 ≤ (44334693697939/100000000000000 : ℝ)^101 := by
    have hnat : (336990551 : ℕ)^133*100000000000000^101 ≤ 44334693697939^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336990551 625000000 44334693697939 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284440313/10000000000 : ℝ), (-2060291047/10000000000 : ℝ), (336990551/625000000 : ℝ)] ![(21587696676887/50000000000000 : ℝ), (12489912936661/100000000000000 : ℝ), (44334693697939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284440313/10000000000 : ℝ)|^133 ≤ (21587696676887/50000000000000 : ℝ)^101
        have hw : |(5284440313/10000000000 : ℝ)|=(5284440313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060291047/10000000000 : ℝ)|^133 ≤ (12489912936661/100000000000000 : ℝ)^101
        have hw : |(-2060291047/10000000000 : ℝ)|=(2060291047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336990551/625000000 : ℝ)|^133 ≤ (44334693697939/100000000000000 : ℝ)^101
        have hw : |(336990551/625000000 : ℝ)|=(336990551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1056888107/2000000000 : ℝ)*x 0 + (5391848569/10000000000 : ℝ)*x 1 + (-1030145541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056888107/2000000000 : ℝ)^133 ≤ (5396924467781/12500000000000 : ℝ)^101 := by
    have hnat : (1056888107 : ℕ)^133*12500000000000^101 ≤ 5396924467781^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056888107 2000000000 5396924467781 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391848569/10000000000 : ℝ)^133 ≤ (5541836377937/12500000000000 : ℝ)^101 := by
    have hnat : (5391848569 : ℕ)^133*12500000000000^101 ≤ 5541836377937^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391848569 10000000000 5541836377937 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030145541/5000000000 : ℝ)^133 ≤ (12489913216063/100000000000000 : ℝ)^101 := by
    have hnat : (1030145541 : ℕ)^133*100000000000000^101 ≤ 12489913216063^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030145541 5000000000 12489913216063 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056888107/2000000000 : ℝ), (5391848569/10000000000 : ℝ), (-1030145541/5000000000 : ℝ)] ![(5396924467781/12500000000000 : ℝ), (5541836377937/12500000000000 : ℝ), (12489913216063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056888107/2000000000 : ℝ)|^133 ≤ (5396924467781/12500000000000 : ℝ)^101
        have hw : |(1056888107/2000000000 : ℝ)|=(1056888107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391848569/10000000000 : ℝ)|^133 ≤ (5541836377937/12500000000000 : ℝ)^101
        have hw : |(5391848569/10000000000 : ℝ)|=(5391848569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030145541/5000000000 : ℝ)|^133 ≤ (12489913216063/100000000000000 : ℝ)^101
        have hw : |(-1030145541/5000000000 : ℝ)|=(1030145541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (897623699/2000000000 : ℝ)*x 0 + (2134064829/5000000000 : ℝ)*x 1 + (853625933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897623699/2000000000 : ℝ)^133 ≤ (348198796557/1000000000000 : ℝ)^101 := by
    have hnat : (897623699 : ℕ)^133*1000000000000^101 ≤ 348198796557^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897623699 2000000000 348198796557 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134064829/5000000000 : ℝ)^133 ≤ (1303602405147/4000000000000 : ℝ)^101 := by
    have hnat : (2134064829 : ℕ)^133*4000000000000^101 ≤ 1303602405147^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134064829 5000000000 1303602405147 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853625933/2000000000 : ℝ)^133 ≤ (32590060199059/100000000000000 : ℝ)^101 := by
    have hnat : (853625933 : ℕ)^133*100000000000000^101 ≤ 32590060199059^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853625933 2000000000 32590060199059 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897623699/2000000000 : ℝ), (2134064829/5000000000 : ℝ), (853625933/2000000000 : ℝ)] ![(348198796557/1000000000000 : ℝ), (1303602405147/4000000000000 : ℝ), (32590060199059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897623699/2000000000 : ℝ)|^133 ≤ (348198796557/1000000000000 : ℝ)^101
        have hw : |(897623699/2000000000 : ℝ)|=(897623699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2134064829/5000000000 : ℝ)|^133 ≤ (1303602405147/4000000000000 : ℝ)^101
        have hw : |(2134064829/5000000000 : ℝ)|=(2134064829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(853625933/2000000000 : ℝ)|^133 ≤ (32590060199059/100000000000000 : ℝ)^101
        have hw : |(853625933/2000000000 : ℝ)|=(853625933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-141135219/625000000 : ℝ)*x 0 + (5263801657/10000000000 : ℝ)*x 1 + (82246899/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141135219/625000000 : ℝ)^133 ≤ (14093037734309/100000000000000 : ℝ)^101 := by
    have hnat : (141135219 : ℕ)^133*100000000000000^101 ≤ 14093037734309^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141135219 625000000 14093037734309 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263801657/10000000000 : ℝ)^133 ≤ (42953481774423/100000000000000 : ℝ)^101 := by
    have hnat : (5263801657 : ℕ)^133*100000000000000^101 ≤ 42953481774423^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263801657 10000000000 42953481774423 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82246899/156250000 : ℝ)^133 ≤ (42953480474211/100000000000000 : ℝ)^101 := by
    have hnat : (82246899 : ℕ)^133*100000000000000^101 ≤ 42953480474211^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82246899 156250000 42953480474211 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141135219/625000000 : ℝ), (5263801657/10000000000 : ℝ), (82246899/156250000 : ℝ)] ![(14093037734309/100000000000000 : ℝ), (42953481774423/100000000000000 : ℝ), (42953480474211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141135219/625000000 : ℝ)|^133 ≤ (14093037734309/100000000000000 : ℝ)^101
        have hw : |(-141135219/625000000 : ℝ)|=(141135219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263801657/10000000000 : ℝ)|^133 ≤ (42953481774423/100000000000000 : ℝ)^101
        have hw : |(5263801657/10000000000 : ℝ)|=(5263801657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82246899/156250000 : ℝ)|^133 ≤ (42953480474211/100000000000000 : ℝ)^101
        have hw : |(82246899/156250000 : ℝ)|=(82246899/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5374555049/10000000000 : ℝ)*x 0 + (-422266931/2000000000 : ℝ)*x 1 + (5263801787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374555049/10000000000 : ℝ)^133 ≤ (2207376858207/5000000000000 : ℝ)^101 := by
    have hnat : (5374555049 : ℕ)^133*5000000000000^101 ≤ 2207376858207^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374555049 10000000000 2207376858207 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422266931/2000000000 : ℝ)^133 ≤ (12898979654353/100000000000000 : ℝ)^101 := by
    have hnat : (422266931 : ℕ)^133*100000000000000^101 ≤ 12898979654353^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422266931 2000000000 12898979654353 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263801787/10000000000 : ℝ)^133 ≤ (42953483171347/100000000000000 : ℝ)^101 := by
    have hnat : (5263801787 : ℕ)^133*100000000000000^101 ≤ 42953483171347^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263801787 10000000000 42953483171347 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374555049/10000000000 : ℝ), (-422266931/2000000000 : ℝ), (5263801787/10000000000 : ℝ)] ![(2207376858207/5000000000000 : ℝ), (12898979654353/100000000000000 : ℝ), (42953483171347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374555049/10000000000 : ℝ)|^133 ≤ (2207376858207/5000000000000 : ℝ)^101
        have hw : |(5374555049/10000000000 : ℝ)|=(5374555049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422266931/2000000000 : ℝ)|^133 ≤ (12898979654353/100000000000000 : ℝ)^101
        have hw : |(-422266931/2000000000 : ℝ)|=(422266931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263801787/10000000000 : ℝ)|^133 ≤ (42953483171347/100000000000000 : ℝ)^101
        have hw : |(5263801787/10000000000 : ℝ)|=(5263801787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (167954847/312500000 : ℝ)*x 0 + (5263801451/10000000000 : ℝ)*x 1 + (-527833757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167954847/312500000 : ℝ)^133 ≤ (44147537759057/100000000000000 : ℝ)^101 := by
    have hnat : (167954847 : ℕ)^133*100000000000000^101 ≤ 44147537759057^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167954847 312500000 44147537759057 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263801451/10000000000 : ℝ)^133 ≤ (21476739780419/50000000000000 : ℝ)^101 := by
    have hnat : (5263801451 : ℕ)^133*50000000000000^101 ≤ 21476739780419^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263801451 10000000000 21476739780419 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527833757/2500000000 : ℝ)^133 ≤ (2579796531031/20000000000000 : ℝ)^101 := by
    have hnat : (527833757 : ℕ)^133*20000000000000^101 ≤ 2579796531031^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527833757 2500000000 2579796531031 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167954847/312500000 : ℝ), (5263801451/10000000000 : ℝ), (-527833757/2500000000 : ℝ)] ![(44147537759057/100000000000000 : ℝ), (21476739780419/50000000000000 : ℝ), (2579796531031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167954847/312500000 : ℝ)|^133 ≤ (44147537759057/100000000000000 : ℝ)^101
        have hw : |(167954847/312500000 : ℝ)|=(167954847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263801451/10000000000 : ℝ)|^133 ≤ (21476739780419/50000000000000 : ℝ)^101
        have hw : |(5263801451/10000000000 : ℝ)|=(5263801451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527833757/2500000000 : ℝ)|^133 ≤ (2579796531031/20000000000000 : ℝ)^101
        have hw : |(-527833757/2500000000 : ℝ)|=(527833757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (41886161/100000000 : ℝ)*x 0 + (1104456329/2500000000 : ℝ)*x 1 + (4417825967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41886161/100000000 : ℝ)^133 ≤ (15896464361419/50000000000000 : ℝ)^101 := by
    have hnat : (41886161 : ℕ)^133*50000000000000^101 ≤ 15896464361419^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41886161 100000000 15896464361419 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104456329/2500000000 : ℝ)^133 ≤ (17051766160197/50000000000000 : ℝ)^101 := by
    have hnat : (1104456329 : ℕ)^133*50000000000000^101 ≤ 17051766160197^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104456329 2500000000 17051766160197 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417825967/10000000000 : ℝ)^133 ≤ (17051769469009/50000000000000 : ℝ)^101 := by
    have hnat : (4417825967 : ℕ)^133*50000000000000^101 ≤ 17051769469009^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417825967 10000000000 17051769469009 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41886161/100000000 : ℝ), (1104456329/2500000000 : ℝ), (4417825967/10000000000 : ℝ)] ![(15896464361419/50000000000000 : ℝ), (17051766160197/50000000000000 : ℝ), (17051769469009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41886161/100000000 : ℝ)|^133 ≤ (15896464361419/50000000000000 : ℝ)^101
        have hw : |(41886161/100000000 : ℝ)|=(41886161/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104456329/2500000000 : ℝ)|^133 ≤ (17051766160197/50000000000000 : ℝ)^101
        have hw : |(1104456329/2500000000 : ℝ)|=(1104456329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417825967/10000000000 : ℝ)|^133 ≤ (17051769469009/50000000000000 : ℝ)^101
        have hw : |(4417825967/10000000000 : ℝ)|=(4417825967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_8 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-546472281/2500000000 : ℝ)*x 0 + (1293968377/2500000000 : ℝ)*x 1 + (67573571/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546472281/2500000000 : ℝ)^133 ≤ (3375525604157/25000000000000 : ℝ)^101 := by
    have hnat : (546472281 : ℕ)^133*25000000000000^101 ≤ 3375525604157^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546472281 2500000000 3375525604157 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293968377/2500000000 : ℝ)^133 ≤ (42011154252479/100000000000000 : ℝ)^101 := by
    have hnat : (1293968377 : ℕ)^133*100000000000000^101 ≤ 42011154252479^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293968377 2500000000 42011154252479 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67573571/125000000 : ℝ)^133 ≤ (44486743314927/100000000000000 : ℝ)^101 := by
    have hnat : (67573571 : ℕ)^133*100000000000000^101 ≤ 44486743314927^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67573571 125000000 44486743314927 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546472281/2500000000 : ℝ), (1293968377/2500000000 : ℝ), (67573571/125000000 : ℝ)] ![(3375525604157/25000000000000 : ℝ), (42011154252479/100000000000000 : ℝ), (44486743314927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546472281/2500000000 : ℝ)|^133 ≤ (3375525604157/25000000000000 : ℝ)^101
        have hw : |(-546472281/2500000000 : ℝ)|=(546472281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293968377/2500000000 : ℝ)|^133 ≤ (42011154252479/100000000000000 : ℝ)^101
        have hw : |(1293968377/2500000000 : ℝ)|=(1293968377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67573571/125000000 : ℝ)|^133 ≤ (44486743314927/100000000000000 : ℝ)^101
        have hw : |(67573571/125000000 : ℝ)|=(67573571/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_9 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5274555917/10000000000 : ℝ)*x 0 + (-2054559507/10000000000 : ℝ)*x 1 + (5405885513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274555917/10000000000 : ℝ)^133 ≤ (43069079723379/100000000000000 : ℝ)^101 := by
    have hnat : (5274555917 : ℕ)^133*100000000000000^101 ≤ 43069079723379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274555917 10000000000 43069079723379 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054559507/10000000000 : ℝ)^133 ≤ (19444029311/156250000000 : ℝ)^101 := by
    have hnat : (2054559507 : ℕ)^133*156250000000^101 ≤ 19444029311^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054559507 10000000000 19444029311 156250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405885513/10000000000 : ℝ)^133 ≤ (4448674150521/10000000000000 : ℝ)^101 := by
    have hnat : (5405885513 : ℕ)^133*10000000000000^101 ≤ 4448674150521^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405885513 10000000000 4448674150521 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274555917/10000000000 : ℝ), (-2054559507/10000000000 : ℝ), (5405885513/10000000000 : ℝ)] ![(43069079723379/100000000000000 : ℝ), (19444029311/156250000000 : ℝ), (4448674150521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274555917/10000000000 : ℝ)|^133 ≤ (43069079723379/100000000000000 : ℝ)^101
        have hw : |(5274555917/10000000000 : ℝ)|=(5274555917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054559507/10000000000 : ℝ)|^133 ≤ (19444029311/156250000000 : ℝ)^101
        have hw : |(-2054559507/10000000000 : ℝ)|=(2054559507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405885513/10000000000 : ℝ)|^133 ≤ (4448674150521/10000000000000 : ℝ)^101
        have hw : |(5405885513/10000000000 : ℝ)|=(5405885513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_10 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1318638951/2500000000 : ℝ)*x 0 + (675735679/1250000000 : ℝ)*x 1 + (-256819971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318638951/2500000000 : ℝ)^133 ≤ (8613815701669/20000000000000 : ℝ)^101 := by
    have hnat : (1318638951 : ℕ)^133*20000000000000^101 ≤ 8613815701669^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318638951 2500000000 8613815701669 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675735679/1250000000 : ℝ)^133 ≤ (11121685156861/25000000000000 : ℝ)^101 := by
    have hnat : (675735679 : ℕ)^133*25000000000000^101 ≤ 11121685156861^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675735679 1250000000 11121685156861 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256819971/1250000000 : ℝ)^133 ≤ (12444180840741/100000000000000 : ℝ)^101 := by
    have hnat : (256819971 : ℕ)^133*100000000000000^101 ≤ 12444180840741^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256819971 1250000000 12444180840741 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318638951/2500000000 : ℝ), (675735679/1250000000 : ℝ), (-256819971/1250000000 : ℝ)] ![(8613815701669/20000000000000 : ℝ), (11121685156861/25000000000000 : ℝ), (12444180840741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318638951/2500000000 : ℝ)|^133 ≤ (8613815701669/20000000000000 : ℝ)^101
        have hw : |(1318638951/2500000000 : ℝ)|=(1318638951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675735679/1250000000 : ℝ)|^133 ≤ (11121685156861/25000000000000 : ℝ)^101
        have hw : |(675735679/1250000000 : ℝ)|=(675735679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256819971/1250000000 : ℝ)|^133 ≤ (12444180840741/100000000000000 : ℝ)^101
        have hw : |(-256819971/1250000000 : ℝ)|=(256819971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_11 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (904078119/2000000000 : ℝ)*x 0 + (425170563/1000000000 : ℝ)*x 1 + (4251706271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904078119/2000000000 : ℝ)^133 ≤ (4393744467743/12500000000000 : ℝ)^101 := by
    have hnat : (904078119 : ℕ)^133*12500000000000^101 ≤ 4393744467743^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904078119 2000000000 4393744467743 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425170563/1000000000 : ℝ)^133 ≤ (8106254725289/25000000000000 : ℝ)^101 := by
    have hnat : (425170563 : ℕ)^133*25000000000000^101 ≤ 8106254725289^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425170563 1000000000 8106254725289 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251706271/10000000000 : ℝ)^133 ≤ (405312816731/1250000000000 : ℝ)^101 := by
    have hnat : (4251706271 : ℕ)^133*1250000000000^101 ≤ 405312816731^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251706271 10000000000 405312816731 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904078119/2000000000 : ℝ), (425170563/1000000000 : ℝ), (4251706271/10000000000 : ℝ)] ![(4393744467743/12500000000000 : ℝ), (8106254725289/25000000000000 : ℝ), (405312816731/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904078119/2000000000 : ℝ)|^133 ≤ (4393744467743/12500000000000 : ℝ)^101
        have hw : |(904078119/2000000000 : ℝ)|=(904078119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425170563/1000000000 : ℝ)|^133 ≤ (8106254725289/25000000000000 : ℝ)^101
        have hw : |(425170563/1000000000 : ℝ)|=(425170563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251706271/10000000000 : ℝ)|^133 ≤ (405312816731/1250000000000 : ℝ)^101
        have hw : |(4251706271/10000000000 : ℝ)|=(4251706271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_12 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-496521603/2500000000 : ℝ)*x 0 + (5477462599/10000000000 : ℝ)*x 1 + (5252774699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496521603/2500000000 : ℝ)^133 ≤ (1487619019681/12500000000000 : ℝ)^101 := by
    have hnat : (496521603 : ℕ)^133*12500000000000^101 ≤ 1487619019681^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496521603 2500000000 1487619019681 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477462599/10000000000 : ℝ)^133 ≤ (45264017569851/100000000000000 : ℝ)^101 := by
    have hnat : (5477462599 : ℕ)^133*100000000000000^101 ≤ 45264017569851^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477462599 10000000000 45264017569851 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252774699/10000000000 : ℝ)^133 ≤ (42835030257551/100000000000000 : ℝ)^101 := by
    have hnat : (5252774699 : ℕ)^133*100000000000000^101 ≤ 42835030257551^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252774699 10000000000 42835030257551 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496521603/2500000000 : ℝ), (5477462599/10000000000 : ℝ), (5252774699/10000000000 : ℝ)] ![(1487619019681/12500000000000 : ℝ), (45264017569851/100000000000000 : ℝ), (42835030257551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496521603/2500000000 : ℝ)|^133 ≤ (1487619019681/12500000000000 : ℝ)^101
        have hw : |(-496521603/2500000000 : ℝ)|=(496521603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477462599/10000000000 : ℝ)|^133 ≤ (45264017569851/100000000000000 : ℝ)^101
        have hw : |(5477462599/10000000000 : ℝ)|=(5477462599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252774699/10000000000 : ℝ)|^133 ≤ (42835030257551/100000000000000 : ℝ)^101
        have hw : |(5252774699/10000000000 : ℝ)|=(5252774699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_13 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5382312833/10000000000 : ℝ)*x 0 + (-1057812439/5000000000 : ℝ)*x 1 + (2626387073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382312833/10000000000 : ℝ)^133 ≤ (44231469861143/100000000000000 : ℝ)^101 := by
    have hnat : (5382312833 : ℕ)^133*100000000000000^101 ≤ 44231469861143^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382312833 10000000000 44231469861143 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057812439/5000000000 : ℝ)^133 ≤ (12933505802363/100000000000000 : ℝ)^101 := by
    have hnat : (1057812439 : ℕ)^133*100000000000000^101 ≤ 12933505802363^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057812439 5000000000 12933505802363 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626387073/5000000000 : ℝ)^133 ≤ (21417512159601/50000000000000 : ℝ)^101 := by
    have hnat : (2626387073 : ℕ)^133*50000000000000^101 ≤ 21417512159601^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626387073 5000000000 21417512159601 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382312833/10000000000 : ℝ), (-1057812439/5000000000 : ℝ), (2626387073/5000000000 : ℝ)] ![(44231469861143/100000000000000 : ℝ), (12933505802363/100000000000000 : ℝ), (21417512159601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382312833/10000000000 : ℝ)|^133 ≤ (44231469861143/100000000000000 : ℝ)^101
        have hw : |(5382312833/10000000000 : ℝ)|=(5382312833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057812439/5000000000 : ℝ)|^133 ≤ (12933505802363/100000000000000 : ℝ)^101
        have hw : |(-1057812439/5000000000 : ℝ)|=(1057812439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626387073/5000000000 : ℝ)|^133 ≤ (21417512159601/50000000000000 : ℝ)^101
        have hw : |(2626387073/5000000000 : ℝ)|=(2626387073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_14 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (538231293/1000000000 : ℝ)*x 0 + (5252774629/10000000000 : ℝ)*x 1 + (-2115624103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538231293/1000000000 : ℝ)^133 ≤ (22115735455421/50000000000000 : ℝ)^101 := by
    have hnat : (538231293 : ℕ)^133*50000000000000^101 ≤ 22115735455421^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538231293 1000000000 22115735455421 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252774629/10000000000 : ℝ)^133 ≤ (42835029505861/100000000000000 : ℝ)^101 := by
    have hnat : (5252774629 : ℕ)^133*100000000000000^101 ≤ 42835029505861^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252774629 10000000000 42835029505861 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115624103/10000000000 : ℝ)^133 ≤ (12933499563441/100000000000000 : ℝ)^101 := by
    have hnat : (2115624103 : ℕ)^133*100000000000000^101 ≤ 12933499563441^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115624103 10000000000 12933499563441 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538231293/1000000000 : ℝ), (5252774629/10000000000 : ℝ), (-2115624103/10000000000 : ℝ)] ![(22115735455421/50000000000000 : ℝ), (42835029505861/100000000000000 : ℝ), (12933499563441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538231293/1000000000 : ℝ)|^133 ≤ (22115735455421/50000000000000 : ℝ)^101
        have hw : |(538231293/1000000000 : ℝ)|=(538231293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252774629/10000000000 : ℝ)|^133 ≤ (42835029505861/100000000000000 : ℝ)^101
        have hw : |(5252774629/10000000000 : ℝ)|=(5252774629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115624103/10000000000 : ℝ)|^133 ≤ (12933499563441/100000000000000 : ℝ)^101
        have hw : |(-2115624103/10000000000 : ℝ)|=(2115624103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_box_15 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1040594083/2500000000 : ℝ)*x 0 + (177228289/400000000 : ℝ)*x 1 + (886141417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040594083/2500000000 : ℝ)^133 ≤ (6306183678999/20000000000000 : ℝ)^101 := by
    have hnat : (1040594083 : ℕ)^133*20000000000000^101 ≤ 6306183678999^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040594083 2500000000 6306183678999 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177228289/400000000 : ℝ)^133 ≤ (8558635376741/25000000000000 : ℝ)^101 := by
    have hnat : (177228289 : ℕ)^133*25000000000000^101 ≤ 8558635376741^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177228289 400000000 8558635376741 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886141417/2000000000 : ℝ)^133 ≤ (17117270041253/50000000000000 : ℝ)^101 := by
    have hnat : (886141417 : ℕ)^133*50000000000000^101 ≤ 17117270041253^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886141417 2000000000 17117270041253 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040594083/2500000000 : ℝ), (177228289/400000000 : ℝ), (886141417/2000000000 : ℝ)] ![(6306183678999/20000000000000 : ℝ), (8558635376741/25000000000000 : ℝ), (17117270041253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040594083/2500000000 : ℝ)|^133 ≤ (6306183678999/20000000000000 : ℝ)^101
        have hw : |(1040594083/2500000000 : ℝ)|=(1040594083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177228289/400000000 : ℝ)|^133 ≤ (8558635376741/25000000000000 : ℝ)^101
        have hw : |(177228289/400000000 : ℝ)|=(177228289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886141417/2000000000 : ℝ)|^133 ≤ (17117270041253/50000000000000 : ℝ)^101
        have hw : |(886141417/2000000000 : ℝ)|=(886141417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1571/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58853/100000 : ℝ) ∧ (79681/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84171/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5519/50000 : ℝ) ^ (4255/1024 : ℝ) ≤ (5271301584380253/50000000000000000000 : ℝ) := by
    have hpowers : (5519/50000 : ℝ)^4255 ≤ (5271301584380253/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5519 : ℕ)^4255*50000000000000000000^1024 ≤ 5271301584380253^1024*50000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5519 50000 5271301584380253 50000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5519/50000 : ℝ)) (X := (5271301584380253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (587/4000 : ℝ) ^ (4255/1024 : ℝ) ≤ (1377095785754911/4000000000000000000 : ℝ) := by
    have hpowers : (587/4000 : ℝ)^4255 ≤ (1377095785754911/4000000000000000000 : ℝ)^1024 := by
      have hnat : (587 : ℕ)^4255*4000000000000000000^1024 ≤ 1377095785754911^1024*4000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 4000 1377095785754911 4000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/4000 : ℝ)) (X := (1377095785754911/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005271301584380253/25000000000000000000 : ℝ) ≤ (5000253695922779/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (25005271301584380253/25000000000000000000 : ℝ)^1024 ≤ (5000253695922779/5000000000000000 : ℝ)^4255 := by
      have hnat : (25005271301584380253 : ℕ)^1024*5000000000000000^4255 ≤ 5000253695922779^4255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005271301584380253 25000000000000000000 5000253695922779 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000253695922779/5000000000000000 : ℝ)) (X := (25005271301584380253/25000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044969997812633281/100000000000000000000 : ℝ) ≤ (1250135256808079/1250000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (100044969997812633281/100000000000000000000 : ℝ)^1024 ≤ (1250135256808079/1250000000000000 : ℝ)^4255 := by
      have hnat : (100044969997812633281 : ℕ)^1024*1250000000000000^4255 ≤ 1250135256808079^4255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044969997812633281 100000000000000000000 1250135256808079 1250000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250135256808079/1250000000000000 : ℝ)) (X := (100044969997812633281/100000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001377095785754911/2000000000000000000 : ℝ) ≤ (5000828358541853/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (2001377095785754911/2000000000000000000 : ℝ)^1024 ≤ (5000828358541853/5000000000000000 : ℝ)^4255 := by
      have hnat : (2001377095785754911 : ℕ)^1024*5000000000000000^4255 ≤ 5000828358541853^4255*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001377095785754911 2000000000000000000 5000828358541853 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000828358541853/5000000000000000 : ℝ)) (X := (2001377095785754911/2000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5271301584380253/50000000000000000000 : ℝ) ≤ ((18179579566081808411/18185000000000000000 : ℝ)+2*(287331309537/181850000000000 : ℝ)*(5519/50000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (18179579566081808411/18185000000000000000 : ℝ)+2*(287331309537/181850000000000 : ℝ)*(5519/50000 : ℝ)=(5000253695922779/5000000000000000 : ℝ) by norm_num, show 1+2*(5271301584380253/50000000000000000000 : ℝ)=(25005271301584380253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1377095785754911/4000000000000000000 : ℝ)+(5271301584380253/50000000000000000000 : ℝ) ≤ ((18179579566081808411/18185000000000000000 : ℝ)+(287331309537/181850000000000 : ℝ)*((587/4000 : ℝ)+(5519/50000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (18179579566081808411/18185000000000000000 : ℝ)+(287331309537/181850000000000 : ℝ)*((587/4000 : ℝ)+(5519/50000 : ℝ))=(1250135256808079/1250000000000000 : ℝ) by norm_num, show 1+(1377095785754911/4000000000000000000 : ℝ)+(5271301584380253/50000000000000000000 : ℝ)=(100044969997812633281/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1377095785754911/4000000000000000000 : ℝ) ≤ ((18179579566081808411/18185000000000000000 : ℝ)+2*(287331309537/181850000000000 : ℝ)*(587/4000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (18179579566081808411/18185000000000000000 : ℝ)+2*(287331309537/181850000000000 : ℝ)*(587/4000 : ℝ)=(5000828358541853/5000000000000000 : ℝ) by norm_num, show 1+2*(1377095785754911/4000000000000000000 : ℝ)=(2001377095785754911/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18179579566081808411/18185000000000000000 : ℝ)*(X 1 0+X 2 0)+(287331309537/181850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (18179579566081808411/18185000000000000000 : ℝ)) (alpha := (287331309537/181850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18179579566081808411/18185000000000000000 : ℝ)*(X 0 1+X 2 1)+(287331309537/181850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (18179579566081808411/18185000000000000000 : ℝ)) (alpha := (287331309537/181850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18179579566081808411/18185000000000000000 : ℝ)*(X 0 2+X 1 2)+(287331309537/181850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (18179579566081808411/18185000000000000000 : ℝ)) (alpha := (287331309537/181850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1913381663/10000000000 : ℝ)*X 0 0+(1347962127/2500000000 : ℝ)*X 0 1+(2695924307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284440313/10000000000 : ℝ)*X 1 0+(-2060291047/10000000000 : ℝ)*X 1 1+(336990551/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056888107/2000000000 : ℝ)*X 2 0+(5391848569/10000000000 : ℝ)*X 2 1+(-1030145541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((897623699/2000000000 : ℝ)*X 0 0+(2134064829/5000000000 : ℝ)*X 0 1+(853625933/2000000000 : ℝ)*X 0 2+(897623699/2000000000 : ℝ)*X 1 0+(2134064829/5000000000 : ℝ)*X 1 1+(853625933/2000000000 : ℝ)*X 1 2+(897623699/2000000000 : ℝ)*X 2 0+(2134064829/5000000000 : ℝ)*X 2 1+(853625933/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-141135219/625000000 : ℝ)*X 0 0+(5263801657/10000000000 : ℝ)*X 0 1+(82246899/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374555049/10000000000 : ℝ)*X 1 0+(-422266931/2000000000 : ℝ)*X 1 1+(5263801787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167954847/312500000 : ℝ)*X 2 0+(5263801451/10000000000 : ℝ)*X 2 1+(-527833757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((41886161/100000000 : ℝ)*X 0 0+(1104456329/2500000000 : ℝ)*X 0 1+(4417825967/10000000000 : ℝ)*X 0 2+(41886161/100000000 : ℝ)*X 1 0+(1104456329/2500000000 : ℝ)*X 1 1+(4417825967/10000000000 : ℝ)*X 1 2+(41886161/100000000 : ℝ)*X 2 0+(1104456329/2500000000 : ℝ)*X 2 1+(4417825967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-546472281/2500000000 : ℝ)*X 0 0+(1293968377/2500000000 : ℝ)*X 0 1+(67573571/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274555917/10000000000 : ℝ)*X 1 0+(-2054559507/10000000000 : ℝ)*X 1 1+(5405885513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318638951/2500000000 : ℝ)*X 2 0+(675735679/1250000000 : ℝ)*X 2 1+(-256819971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((904078119/2000000000 : ℝ)*X 0 0+(425170563/1000000000 : ℝ)*X 0 1+(4251706271/10000000000 : ℝ)*X 0 2+(904078119/2000000000 : ℝ)*X 1 0+(425170563/1000000000 : ℝ)*X 1 1+(4251706271/10000000000 : ℝ)*X 1 2+(904078119/2000000000 : ℝ)*X 2 0+(425170563/1000000000 : ℝ)*X 2 1+(4251706271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-496521603/2500000000 : ℝ)*X 0 0+(5477462599/10000000000 : ℝ)*X 0 1+(5252774699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382312833/10000000000 : ℝ)*X 1 0+(-1057812439/5000000000 : ℝ)*X 1 1+(2626387073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((538231293/1000000000 : ℝ)*X 2 0+(5252774629/10000000000 : ℝ)*X 2 1+(-2115624103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1040594083/2500000000 : ℝ)*X 0 0+(177228289/400000000 : ℝ)*X 0 1+(886141417/2000000000 : ℝ)*X 0 2+(1040594083/2500000000 : ℝ)*X 1 0+(177228289/400000000 : ℝ)*X 1 1+(886141417/2000000000 : ℝ)*X 1 2+(1040594083/2500000000 : ℝ)*X 2 0+(177228289/400000000 : ℝ)*X 2 1+(886141417/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1571/2500 : ℝ) ≤ (-7141904774425182194456908331511/11365625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316993/20000000000000 : ℝ)*(upper1) + (26399269/100000000000000 : ℝ)*(upper2) + (67948553/50000000000000 : ℝ)*(lower4) + (40994051/50000000000000 : ℝ)*(upper5) + (71715087856117/2500000000000 : ℝ)*(major0) + (71715087856117/2500000000000 : ℝ)*(major1) + (71715087856117/2500000000000 : ℝ)*(major2) + (12648668313/100000000000000 : ℝ)*(sp2) + (3717369511/100000000000000 : ℝ)*(sp3) + (970563723943301/25000000000000 : ℝ)*(sp4) + (970541273638039/25000000000000 : ℝ)*(sp5) + (3882242247104891/100000000000000 : ℝ)*(sp6) + (1875894337148639/100000000000000 : ℝ)*(sp7) + (11225152631/12500000000000 : ℝ)*(sp13) + (37517961090363/2000000000000 : ℝ)*(f.failure) + (970563723943301/25000000000000 : ℝ)*(f.sum) + (1964436739209/3637000000000000000000000000 : ℝ)*base66 + (140856292739074913/45462500000000000000000000000000 : ℝ)*base68 + (300489434613000087/45462500000000000000000000000000 : ℝ)*base69 + (224851454782537587/45462500000000000000000000000000 : ℝ)*base71 + (8868428776771/1818500000000000000000000000 : ℝ)*base74 + (220471505016350087/45462500000000000000000000000000 : ℝ)*base75 + (225263504560450087/45462500000000000000000000000000 : ℝ)*base77 + (64257236302550087/45462500000000000000000000000000 : ℝ)*base79 + (8306225455677/1818500000000000000000000000 : ℝ)*base82 + (74593/40000000000000000000 : ℝ)*base90 + (74593/40000000000000000000 : ℝ)*base92 + (74593/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58853/100000 : ℝ) ≤ (6689255623355240905317036709191/11365625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6004703/50000000000000 : ℝ)*(lower3) + (22520353/100000000000000 : ℝ)*(upper4) + (1532617/12500000000000 : ℝ)*(upper5) + (573391419657/19531250000 : ℝ)*(major0) + (573391419657/19531250000 : ℝ)*(major1) + (573391419657/19531250000 : ℝ)*(major2) + (3932092096757841/100000000000000 : ℝ)*(sp0) + (122877653393093/3125000000000 : ℝ)*(sp1) + (1966046048157591/50000000000000 : ℝ)*(sp2) + (479954222104337/25000000000000 : ℝ)*(sp3) + (967083943/12500000000000 : ℝ)*(sp5) + (548935339/100000000000000 : ℝ)*(sp6) + (220341701/100000000000000 : ℝ)*(sp7) + (548492679/100000000000000 : ℝ)*(sp12) + (239977138594881/12500000000000 : ℝ)*(f.failure) + (98302316131263/2500000000000 : ℝ)*(f.sum) + (7504050214641/3637000000000000000000000000 : ℝ)*base66 + (94388313129230239/11365625000000000000000000000000 : ℝ)*base67 + (19621601380105193/5682812500000000000000000000000 : ℝ)*base70 + (186352456374483/1420703125000000000000000000000 : ℝ)*base71 + (1760410728159/909250000000000000000000000 : ℝ)*base73 + (40316961593811489/11365625000000000000000000000000 : ℝ)*base75 + (997153490180193/5682812500000000000000000000000 : ℝ)*base78 + (20601681159773989/11365625000000000000000000000000 : ℝ)*base79 + (875440752201/727400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3015891/250000000000000000000 : ℝ)*base90 + (3015891/250000000000000000000 : ℝ)*base92 + (3015891/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79681/100000 : ℝ) ≤ (181129882641910444263387008868417/227312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47354013/100000000000000 : ℝ)*(upper0) + (149327749/100000000000000 : ℝ)*(upper2) + (58603337/100000000000000 : ℝ)*(lower3) + (1569663/6250000000000 : ℝ)*(lower5) + (1624803778508451/50000000000000 : ℝ)*(major0) + (1624803778508451/50000000000000 : ℝ)*(major1) + (1624803778508451/50000000000000 : ℝ)*(major2) + (25342936669/25000000000000 : ℝ)*(sp1) + (36703505561/100000000000000 : ℝ)*(sp3) + (2750026433/25000000000000 : ℝ)*(sp4) + (4347590746544323/100000000000000 : ℝ)*(sp8) + (4347500374903379/100000000000000 : ℝ)*(sp9) + (869520349330011/20000000000000 : ℝ)*(sp10) + (33203368686629/1562500000000 : ℝ)*(sp11) + (1062526149724909/50000000000000 : ℝ)*(f.failure) + (869520349330011/20000000000000 : ℝ)*(f.sum) + (64051273077273/18185000000000000000000000000 : ℝ)*base65 + (8152119557204581361/909250000000000000000000000000000 : ℝ)*base67 + (2035764830589831361/909250000000000000000000000000000 : ℝ)*base69 + (8517880172294581361/909250000000000000000000000000000 : ℝ)*base71 + (22779018801457/18185000000000000000000000000 : ℝ)*base74 + (8674758222968081361/909250000000000000000000000000000 : ℝ)*base75 + (3724972388371331361/909250000000000000000000000000000 : ℝ)*base77 + (4473913022801418639/909250000000000000000000000000000 : ℝ)*base80 + (4457698731437/18185000000000000000000000000 : ℝ)*base82 + (4900201/1000000000000000000000 : ℝ)*base89 + (4900201/1000000000000000000000 : ℝ)*base91 + (4900201/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84171/100000 : ℝ) ≤ (-382650364176734571404343548941611/454625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128279293/100000000000000 : ℝ)*(lower1) + (83597427/25000000000000 : ℝ)*(lower2) + (12760019/50000000000000 : ℝ)*(upper5) + (1642782303859311/50000000000000 : ℝ)*(major0) + (1642782303859311/50000000000000 : ℝ)*(major1) + (1642782303859311/50000000000000 : ℝ)*(major2) + (5573031181/100000000000000 : ℝ)*(sp0) + (409792868157/100000000000000 : ℝ)*(sp5) + (34403651791/100000000000000 : ℝ)*(sp6) + (13350356241/10000000000000 : ℝ)*(sp7) + (2225306831290289/50000000000000 : ℝ)*(sp12) + (2225104721371801/50000000000000 : ℝ)*(sp13) + (139080775998749/3125000000000 : ℝ)*(sp14) + (429686518629781/20000000000000 : ℝ)*(sp15) + (429713219342263/20000000000000 : ℝ)*(f.failure) + (55632740445147/1250000000000 : ℝ)*(f.sum) + (49413739613643/18185000000000000000000000000 : ℝ)*base65 + (1699211612482585179/909250000000000000000000000000000 : ℝ)*base68 + (5711351064945585179/909250000000000000000000000000000 : ℝ)*base70 + (5697180465524585179/909250000000000000000000000000000 : ℝ)*base72 + (26973434813569/9092500000000000000000000000 : ℝ)*base73 + (7842343282424335179/909250000000000000000000000000000 : ℝ)*base76 + (3331001315715835179/909250000000000000000000000000000 : ℝ)*base78 + (6506844112780335179/909250000000000000000000000000000 : ℝ)*base80 + (54315120441573/18185000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2374507/400000000000000000000 : ℝ)*base89 + (2374507/400000000000000000000 : ℝ)*base91 + (2374507/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1296_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58853/100000 : ℝ) else (79681/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84171/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1296_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1296_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58853/100000 : ℝ) else (79681/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84171/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1296_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1296_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1296_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58853/100000 : ℝ) else (79681/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84171/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
