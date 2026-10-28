-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:18.147771+00:00
-- url     : https://prove2.me/submissions/c1925baf-5ba8-4d0c-80dd-8dd13b6e6f53

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
theorem support_rectangle_w1271_s9_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106882669/200000000 : ℝ)*x 0 + (-2168555751/10000000000 : ℝ)*x 1 + (105352967/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106882669/200000000 : ℝ)^8465 ≤ (21877551991553/50000000000000 : ℝ)^6417 := by
    have hnat : (106882669 : ℕ)^8465*50000000000000^6417 ≤ 21877551991553^6417*200000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106882669 200000000 21877551991553 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168555751/10000000000 : ℝ)^8465 ≤ (13313981261423/100000000000000 : ℝ)^6417 := by
    have hnat : (2168555751 : ℕ)^8465*100000000000000^6417 ≤ 13313981261423^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168555751 10000000000 13313981261423 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105352967/200000000 : ℝ)^8465 ≤ (858618294817/2000000000000 : ℝ)^6417 := by
    have hnat : (105352967 : ℕ)^8465*2000000000000^6417 ≤ 858618294817^6417*200000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105352967 200000000 858618294817 2000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106882669/200000000 : ℝ), (-2168555751/10000000000 : ℝ), (105352967/200000000 : ℝ)] ![(21877551991553/50000000000000 : ℝ), (13313981261423/100000000000000 : ℝ), (858618294817/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106882669/200000000 : ℝ)|^8465 ≤ (21877551991553/50000000000000 : ℝ)^6417
        have hw : |(106882669/200000000 : ℝ)|=(106882669/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168555751/10000000000 : ℝ)|^8465 ≤ (13313981261423/100000000000000 : ℝ)^6417
        have hw : |(-2168555751/10000000000 : ℝ)|=(2168555751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105352967/200000000 : ℝ)|^8465 ≤ (858618294817/2000000000000 : ℝ)^6417
        have hw : |(105352967/200000000 : ℝ)|=(105352967/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s9_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869335497/2000000000 : ℝ)*x 0 + (131968849/312500000 : ℝ)*x 1 + (2236922917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869335497/2000000000 : ℝ)^8465 ≤ (33317663882141/100000000000000 : ℝ)^6417 := by
    have hnat : (869335497 : ℕ)^8465*100000000000000^6417 ≤ 33317663882141^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869335497 2000000000 33317663882141 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131968849/312500000 : ℝ)^8465 ≤ (6414571228297/20000000000000 : ℝ)^6417 := by
    have hnat : (131968849 : ℕ)^8465*20000000000000^6417 ≤ 6414571228297^6417*312500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131968849 312500000 6414571228297 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236922917/5000000000 : ℝ)^8465 ≤ (17304739980171/50000000000000 : ℝ)^6417 := by
    have hnat : (2236922917 : ℕ)^8465*50000000000000^6417 ≤ 17304739980171^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236922917 5000000000 17304739980171 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869335497/2000000000 : ℝ), (131968849/312500000 : ℝ), (2236922917/5000000000 : ℝ)] ![(33317663882141/100000000000000 : ℝ), (6414571228297/20000000000000 : ℝ), (17304739980171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869335497/2000000000 : ℝ)|^8465 ≤ (33317663882141/100000000000000 : ℝ)^6417
        have hw : |(869335497/2000000000 : ℝ)|=(869335497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131968849/312500000 : ℝ)|^8465 ≤ (6414571228297/20000000000000 : ℝ)^6417
        have hw : |(131968849/312500000 : ℝ)|=(131968849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236922917/5000000000 : ℝ)|^8465 ≤ (17304739980171/50000000000000 : ℝ)^6417
        have hw : |(2236922917/5000000000 : ℝ)|=(2236922917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s9_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106232627/10000000000 : ℝ)*x 0 + (164623717/312500000 : ℝ)*x 1 + (1347569827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106232627/10000000000 : ℝ)^8465 ≤ (12811555425981/100000000000000 : ℝ)^6417 := by
    have hnat : (2106232627 : ℕ)^8465*100000000000000^6417 ≤ 12811555425981^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106232627 10000000000 12811555425981 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164623717/312500000 : ℝ)^8465 ≤ (21467126981983/50000000000000 : ℝ)^6417 := by
    have hnat : (164623717 : ℕ)^8465*50000000000000^6417 ≤ 21467126981983^6417*312500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164623717 312500000 21467126981983 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347569827/2500000000 : ℝ)^8465 ≤ (44254190592287/100000000000000 : ℝ)^6417 := by
    have hnat : (1347569827 : ℕ)^8465*100000000000000^6417 ≤ 44254190592287^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347569827 2500000000 44254190592287 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106232627/10000000000 : ℝ), (164623717/312500000 : ℝ), (1347569827/2500000000 : ℝ)] ![(12811555425981/100000000000000 : ℝ), (21467126981983/50000000000000 : ℝ), (44254190592287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106232627/10000000000 : ℝ)|^8465 ≤ (12811555425981/100000000000000 : ℝ)^6417
        have hw : |(-2106232627/10000000000 : ℝ)|=(2106232627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164623717/312500000 : ℝ)|^8465 ≤ (21467126981983/50000000000000 : ℝ)^6417
        have hw : |(164623717/312500000 : ℝ)|=(164623717/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347569827/2500000000 : ℝ)|^8465 ≤ (44254190592287/100000000000000 : ℝ)^6417
        have hw : |(1347569827/2500000000 : ℝ)|=(1347569827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s9_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312701/10000000 : ℝ)*x 0 + (-2045924401/10000000000 : ℝ)*x 1 + (5390279871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312701/10000000 : ℝ)^8465 ≤ (347327479389/800000000000 : ℝ)^6417 := by
    have hnat : (5312701 : ℕ)^8465*800000000000^6417 ≤ 347327479389^6417*10000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312701 10000000 347327479389 800000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045924401/10000000000 : ℝ)^8465 ≤ (493194734999/4000000000000 : ℝ)^6417 := by
    have hnat : (2045924401 : ℕ)^8465*4000000000000^6417 ≤ 493194734999^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045924401 10000000000 493194734999 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390279871/10000000000 : ℝ)^8465 ≤ (2765887293107/6250000000000 : ℝ)^6417 := by
    have hnat : (5390279871 : ℕ)^8465*6250000000000^6417 ≤ 2765887293107^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390279871 10000000000 2765887293107 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312701/10000000 : ℝ), (-2045924401/10000000000 : ℝ), (5390279871/10000000000 : ℝ)] ![(347327479389/800000000000 : ℝ), (493194734999/4000000000000 : ℝ), (2765887293107/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312701/10000000 : ℝ)|^8465 ≤ (347327479389/800000000000 : ℝ)^6417
        have hw : |(5312701/10000000 : ℝ)|=(5312701/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045924401/10000000000 : ℝ)|^8465 ≤ (493194734999/4000000000000 : ℝ)^6417
        have hw : |(-2045924401/10000000000 : ℝ)|=(2045924401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390279871/10000000000 : ℝ)|^8465 ≤ (2765887293107/6250000000000 : ℝ)^6417
        have hw : |(5390279871/10000000000 : ℝ)|=(5390279871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s9_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312701267/10000000000 : ℝ)*x 0 + (2695139751/5000000000 : ℝ)*x 1 + (-1022962271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312701267/10000000000 : ℝ)^8465 ≤ (43415937801951/100000000000000 : ℝ)^6417 := by
    have hnat : (5312701267 : ℕ)^8465*100000000000000^6417 ≤ 43415937801951^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312701267 10000000000 43415937801951 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695139751/5000000000 : ℝ)^8465 ≤ (44254192693353/100000000000000 : ℝ)^6417 := by
    have hnat : (2695139751 : ℕ)^8465*100000000000000^6417 ≤ 44254192693353^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695139751 5000000000 44254192693353 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022962271/5000000000 : ℝ)^8465 ≤ (3082467373979/25000000000000 : ℝ)^6417 := by
    have hnat : (1022962271 : ℕ)^8465*25000000000000^6417 ≤ 3082467373979^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022962271 5000000000 3082467373979 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312701267/10000000000 : ℝ), (2695139751/5000000000 : ℝ), (-1022962271/5000000000 : ℝ)] ![(43415937801951/100000000000000 : ℝ), (44254192693353/100000000000000 : ℝ), (3082467373979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312701267/10000000000 : ℝ)|^8465 ≤ (43415937801951/100000000000000 : ℝ)^6417
        have hw : |(5312701267/10000000000 : ℝ)|=(5312701267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695139751/5000000000 : ℝ)|^8465 ≤ (44254192693353/100000000000000 : ℝ)^6417
        have hw : |(2695139751/5000000000 : ℝ)|=(2695139751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022962271/5000000000 : ℝ)|^8465 ≤ (3082467373979/25000000000000 : ℝ)^6417
        have hw : |(-1022962271/5000000000 : ℝ)|=(1022962271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s9_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086671653/2500000000 : ℝ)*x 0 + (559151669/1250000000 : ℝ)*x 1 + (1055909541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086671653/2500000000 : ℝ)^8465 ≤ (33317756169081/100000000000000 : ℝ)^6417 := by
    have hnat : (1086671653 : ℕ)^8465*100000000000000^6417 ≤ 33317756169081^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086671653 2500000000 33317756169081 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559151669/1250000000 : ℝ)^8465 ≤ (2162689105437/6250000000000 : ℝ)^6417 := by
    have hnat : (559151669 : ℕ)^8465*6250000000000^6417 ≤ 2162689105437^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559151669 1250000000 2162689105437 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055909541/2500000000 : ℝ)^8465 ≤ (8019804531333/25000000000000 : ℝ)^6417 := by
    have hnat : (1055909541 : ℕ)^8465*25000000000000^6417 ≤ 8019804531333^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055909541 2500000000 8019804531333 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086671653/2500000000 : ℝ), (559151669/1250000000 : ℝ), (1055909541/2500000000 : ℝ)] ![(33317756169081/100000000000000 : ℝ), (2162689105437/6250000000000 : ℝ), (8019804531333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086671653/2500000000 : ℝ)|^8465 ≤ (33317756169081/100000000000000 : ℝ)^6417
        have hw : |(1086671653/2500000000 : ℝ)|=(1086671653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559151669/1250000000 : ℝ)|^8465 ≤ (2162689105437/6250000000000 : ℝ)^6417
        have hw : |(559151669/1250000000 : ℝ)|=(559151669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055909541/2500000000 : ℝ)|^8465 ≤ (8019804531333/25000000000000 : ℝ)^6417
        have hw : |(1055909541/2500000000 : ℝ)|=(1055909541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2303/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2303/20000 : ℝ) ^ (529/128 : ℝ) ≤ (13194103499835267/100000000000000000000 : ℝ) := by
    have hpowers : (2303/20000 : ℝ)^529 ≤ (13194103499835267/100000000000000000000 : ℝ)^128 := by
      have hnat : (2303 : ℕ)^529*100000000000000000000^128 ≤ 13194103499835267^128*20000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2303 20000 13194103499835267 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2303/20000 : ℝ)) (X := (13194103499835267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (529/128 : ℝ) ≤ (15324849277690073/50000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^529 ≤ (15324849277690073/50000000000000000000 : ℝ)^128 := by
      have hnat : (353 : ℕ)^529*50000000000000000000^128 ≤ 15324849277690073^128*2500^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 15324849277690073 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (15324849277690073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013194103499835267/50000000000000000000 : ℝ) ≤ (10000638440968959/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50013194103499835267/50000000000000000000 : ℝ)^128 ≤ (10000638440968959/10000000000000000 : ℝ)^529 := by
      have hnat : (50013194103499835267 : ℕ)^128*10000000000000000^529 ≤ 10000638440968959^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013194103499835267 50000000000000000000 10000638440968959 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000638440968959/10000000000000000 : ℝ)) (X := (50013194103499835267/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043843802055215413/100000000000000000000 : ℝ) ≤ (10001060694579351/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (100043843802055215413/100000000000000000000 : ℝ)^128 ≤ (10001060694579351/10000000000000000 : ℝ)^529 := by
      have hnat : (100043843802055215413 : ℕ)^128*10000000000000000^529 ≤ 10001060694579351^529*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043843802055215413 100000000000000000000 10001060694579351 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001060694579351/10000000000000000 : ℝ)) (X := (100043843802055215413/100000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015324849277690073/25000000000000000000 : ℝ) ≤ (10001482948189743/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25015324849277690073/25000000000000000000 : ℝ)^128 ≤ (10001482948189743/10000000000000000 : ℝ)^529 := by
      have hnat : (25015324849277690073 : ℕ)^128*10000000000000000^529 ≤ 10001482948189743^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015324849277690073 25000000000000000000 10001482948189743 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001482948189743/10000000000000000 : ℝ)) (X := (25015324849277690073/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13194103499835267/100000000000000000000 : ℝ) ≤ ((5208387727615362087/5210000000000000000 : ℝ)+2*(52781701299/32562500000000 : ℝ)*(2303/20000 : ℝ))^(529/128 : ℝ) := by
    rw [show (5208387727615362087/5210000000000000000 : ℝ)+2*(52781701299/32562500000000 : ℝ)*(2303/20000 : ℝ)=(10000638440968959/10000000000000000 : ℝ) by norm_num, show 1+2*(13194103499835267/100000000000000000000 : ℝ)=(50013194103499835267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15324849277690073/50000000000000000000 : ℝ)+(13194103499835267/100000000000000000000 : ℝ) ≤ ((5208387727615362087/5210000000000000000 : ℝ)+(52781701299/32562500000000 : ℝ)*((353/2500 : ℝ)+(2303/20000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (5208387727615362087/5210000000000000000 : ℝ)+(52781701299/32562500000000 : ℝ)*((353/2500 : ℝ)+(2303/20000 : ℝ))=(10001060694579351/10000000000000000 : ℝ) by norm_num, show 1+(15324849277690073/50000000000000000000 : ℝ)+(13194103499835267/100000000000000000000 : ℝ)=(100043843802055215413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15324849277690073/50000000000000000000 : ℝ) ≤ ((5208387727615362087/5210000000000000000 : ℝ)+2*(52781701299/32562500000000 : ℝ)*(353/2500 : ℝ))^(529/128 : ℝ) := by
    rw [show (5208387727615362087/5210000000000000000 : ℝ)+2*(52781701299/32562500000000 : ℝ)*(353/2500 : ℝ)=(10001482948189743/10000000000000000 : ℝ) by norm_num, show 1+2*(15324849277690073/50000000000000000000 : ℝ)=(25015324849277690073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5208387727615362087/5210000000000000000 : ℝ)*(X 1 0+X 2 0)+(52781701299/32562500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (5208387727615362087/5210000000000000000 : ℝ)) (alpha := (52781701299/32562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5208387727615362087/5210000000000000000 : ℝ)*(X 0 1+X 2 1)+(52781701299/32562500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (5208387727615362087/5210000000000000000 : ℝ)) (alpha := (52781701299/32562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5208387727615362087/5210000000000000000 : ℝ)*(X 0 2+X 1 2)+(52781701299/32562500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (5208387727615362087/5210000000000000000 : ℝ)) (alpha := (52781701299/32562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((106882669/200000000 : ℝ)*X 1 0+(-2168555751/10000000000 : ℝ)*X 1 1+(105352967/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((869335497/2000000000 : ℝ)*X 0 0+(131968849/312500000 : ℝ)*X 0 1+(2236922917/5000000000 : ℝ)*X 0 2+(869335497/2000000000 : ℝ)*X 1 0+(131968849/312500000 : ℝ)*X 1 1+(2236922917/5000000000 : ℝ)*X 1 2+(869335497/2000000000 : ℝ)*X 2 0+(131968849/312500000 : ℝ)*X 2 1+(2236922917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2106232627/10000000000 : ℝ)*X 0 0+(164623717/312500000 : ℝ)*X 0 1+(1347569827/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312701/10000000 : ℝ)*X 1 0+(-2045924401/10000000000 : ℝ)*X 1 1+(5390279871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312701267/10000000000 : ℝ)*X 2 0+(2695139751/5000000000 : ℝ)*X 2 1+(-1022962271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1086671653/2500000000 : ℝ)*X 0 0+(559151669/1250000000 : ℝ)*X 0 1+(1055909541/2500000000 : ℝ)*X 0 2+(1086671653/2500000000 : ℝ)*X 1 0+(559151669/1250000000 : ℝ)*X 1 1+(1055909541/2500000000 : ℝ)*X 1 2+(1086671653/2500000000 : ℝ)*X 2 0+(559151669/1250000000 : ℝ)*X 2 1+(1055909541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337170044991473918588608197/130250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (353922151/100000000000000 : ℝ)*(base23) + (8250239/2500000000000 : ℝ)*(lower1) + (2585239/100000000000000 : ℝ)*(lower2) + (71151157/100000000000000 : ℝ)*(upper3) + (3128901/25000000000000 : ℝ)*(upper4) + (6091024015510177/100000000000000 : ℝ)*(major0) + (6091024015510177/100000000000000 : ℝ)*(major1) + (6091024015510177/100000000000000 : ℝ)*(major2) + (1204922367/25000000000000 : ℝ)*(sp0) + (543035351/5000000000000 : ℝ)*(sp1) + (8175227327838137/100000000000000 : ℝ)*(sp2) + (8175222508148669/100000000000000 : ℝ)*(sp3) + (4087613486957993/50000000000000 : ℝ)*(sp4) + (4006809756187239/100000000000000 : ℝ)*(sp5) + (200341030844713/5000000000000 : ℝ)*(f.failure) + (8175227327838137/100000000000000 : ℝ)*(f.sum) + (79428616735659/13025000000000000000000000000 : ℝ)*base65 + (6802267025059860601/521000000000000000000000000000000 : ℝ)*base68 + (14921276389435860601/521000000000000000000000000000000 : ℝ)*base70 + (32057148476851860601/521000000000000000000000000000000 : ℝ)*base72 + (4396037402609/13025000000000000000000000000 : ℝ)*base73 + (3123897102701139399/521000000000000000000000000000000 : ℝ)*base75 + (10319611701753860601/521000000000000000000000000000000 : ℝ)*base78 + (113092764751583860601/521000000000000000000000000000000 : ℝ)*base80 + (2953128908799/814062500000000000000000000 : ℝ)*base81 + (5001357/500000000000000000000 : ℝ)*base89 + (5001357/500000000000000000000 : ℝ)*base91 + (5001357/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1271_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_box_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-198346601/1000000000 : ℝ)*x 0 + (5374383591/10000000000 : ℝ)*x 1 + (5374383739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198346601/1000000000 : ℝ)^8465 ≤ (11835763903451/100000000000000 : ℝ)^6417 := by
    have hnat : (198346601 : ℕ)^8465*100000000000000^6417 ≤ 11835763903451^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198346601 1000000000 11835763903451 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374383591/10000000000 : ℝ)^8465 ≤ (44082117239561/100000000000000 : ℝ)^6417 := by
    have hnat : (5374383591 : ℕ)^8465*100000000000000^6417 ≤ 44082117239561^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374383591 10000000000 44082117239561 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374383739/10000000000 : ℝ)^8465 ≤ (22041059420463/50000000000000 : ℝ)^6417 := by
    have hnat : (5374383739 : ℕ)^8465*50000000000000^6417 ≤ 22041059420463^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374383739 10000000000 22041059420463 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198346601/1000000000 : ℝ), (5374383591/10000000000 : ℝ), (5374383739/10000000000 : ℝ)] ![(11835763903451/100000000000000 : ℝ), (44082117239561/100000000000000 : ℝ), (22041059420463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198346601/1000000000 : ℝ)|^8465 ≤ (11835763903451/100000000000000 : ℝ)^6417
        have hw : |(-198346601/1000000000 : ℝ)|=(198346601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374383591/10000000000 : ℝ)|^8465 ≤ (44082117239561/100000000000000 : ℝ)^6417
        have hw : |(5374383591/10000000000 : ℝ)|=(5374383591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374383739/10000000000 : ℝ)|^8465 ≤ (22041059420463/50000000000000 : ℝ)^6417
        have hw : |(5374383739/10000000000 : ℝ)|=(5374383739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059398981/2000000000 : ℝ)*x 0 + (-2088715137/10000000000 : ℝ)*x 1 + (2687191857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059398981/2000000000 : ℝ)^8465 ≤ (43246699272093/100000000000000 : ℝ)^6417 := by
    have hnat : (1059398981 : ℕ)^8465*100000000000000^6417 ≤ 43246699272093^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059398981 2000000000 43246699272093 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088715137/10000000000 : ℝ)^8465 ≤ (3167795535729/25000000000000 : ℝ)^6417 := by
    have hnat : (2088715137 : ℕ)^8465*25000000000000^6417 ≤ 3167795535729^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088715137 10000000000 3167795535729 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687191857/5000000000 : ℝ)^8465 ≤ (1763284742817/4000000000000 : ℝ)^6417 := by
    have hnat : (2687191857 : ℕ)^8465*4000000000000^6417 ≤ 1763284742817^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687191857 5000000000 1763284742817 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059398981/2000000000 : ℝ), (-2088715137/10000000000 : ℝ), (2687191857/5000000000 : ℝ)] ![(43246699272093/100000000000000 : ℝ), (3167795535729/25000000000000 : ℝ), (1763284742817/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059398981/2000000000 : ℝ)|^8465 ≤ (43246699272093/100000000000000 : ℝ)^6417
        have hw : |(1059398981/2000000000 : ℝ)|=(1059398981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088715137/10000000000 : ℝ)|^8465 ≤ (3167795535729/25000000000000 : ℝ)^6417
        have hw : |(-2088715137/10000000000 : ℝ)|=(2088715137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687191857/5000000000 : ℝ)|^8465 ≤ (1763284742817/4000000000000 : ℝ)^6417
        have hw : |(2687191857/5000000000 : ℝ)|=(2687191857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296994599/10000000000 : ℝ)*x 0 + (1343595953/2500000000 : ℝ)*x 1 + (-2088715417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296994599/10000000000 : ℝ)^8465 ≤ (43246695976453/100000000000000 : ℝ)^6417 := by
    have hnat : (5296994599 : ℕ)^8465*100000000000000^6417 ≤ 43246695976453^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296994599 10000000000 43246695976453 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343595953/2500000000 : ℝ)^8465 ≤ (44082119630789/100000000000000 : ℝ)^6417 := by
    have hnat : (1343595953 : ℕ)^8465*100000000000000^6417 ≤ 44082119630789^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343595953 2500000000 44082119630789 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088715417/10000000000 : ℝ)^8465 ≤ (12671184383653/100000000000000 : ℝ)^6417 := by
    have hnat : (2088715417 : ℕ)^8465*100000000000000^6417 ≤ 12671184383653^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088715417 10000000000 12671184383653 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296994599/10000000000 : ℝ), (1343595953/2500000000 : ℝ), (-2088715417/10000000000 : ℝ)] ![(43246695976453/100000000000000 : ℝ), (44082119630789/100000000000000 : ℝ), (12671184383653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296994599/10000000000 : ℝ)|^8465 ≤ (43246695976453/100000000000000 : ℝ)^6417
        have hw : |(5296994599/10000000000 : ℝ)|=(5296994599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343595953/2500000000 : ℝ)|^8465 ≤ (44082119630789/100000000000000 : ℝ)^6417
        have hw : |(1343595953/2500000000 : ℝ)|=(1343595953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088715417/10000000000 : ℝ)|^8465 ≤ (12671184383653/100000000000000 : ℝ)^6417
        have hw : |(-2088715417/10000000000 : ℝ)|=(2088715417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1113228069/2500000000 : ℝ)*x 0 + (4295582479/10000000000 : ℝ)*x 1 + (53694781/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113228069/2500000000 : ℝ)^8465 ≤ (4299501832401/12500000000000 : ℝ)^6417 := by
    have hnat : (1113228069 : ℕ)^8465*12500000000000^6417 ≤ 4299501832401^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113228069 2500000000 4299501832401 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4295582479/10000000000 : ℝ)^8465 ≤ (1640099633019/5000000000000 : ℝ)^6417 := by
    have hnat : (4295582479 : ℕ)^8465*5000000000000^6417 ≤ 1640099633019^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295582479 10000000000 1640099633019 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53694781/125000000 : ℝ)^8465 ≤ (16400996335227/50000000000000 : ℝ)^6417 := by
    have hnat : (53694781 : ℕ)^8465*50000000000000^6417 ≤ 16400996335227^6417*125000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53694781 125000000 16400996335227 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113228069/2500000000 : ℝ), (4295582479/10000000000 : ℝ), (53694781/125000000 : ℝ)] ![(4299501832401/12500000000000 : ℝ), (1640099633019/5000000000000 : ℝ), (16400996335227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113228069/2500000000 : ℝ)|^8465 ≤ (4299501832401/12500000000000 : ℝ)^6417
        have hw : |(1113228069/2500000000 : ℝ)|=(1113228069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4295582479/10000000000 : ℝ)|^8465 ≤ (1640099633019/5000000000000 : ℝ)^6417
        have hw : |(4295582479/10000000000 : ℝ)|=(4295582479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53694781/125000000 : ℝ)|^8465 ≤ (16400996335227/50000000000000 : ℝ)^6417
        have hw : |(53694781/125000000 : ℝ)|=(53694781/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2230375269/10000000000 : ℝ)*x 0 + (2641291023/5000000000 : ℝ)*x 1 + (528258203/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230375269/10000000000 : ℝ)^8465 ≤ (13816921601059/100000000000000 : ℝ)^6417 := by
    have hnat : (2230375269 : ℕ)^8465*100000000000000^6417 ≤ 13816921601059^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230375269 10000000000 13816921601059 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641291023/5000000000 : ℝ)^8465 ≤ (43091539281511/100000000000000 : ℝ)^6417 := by
    have hnat : (2641291023 : ℕ)^8465*100000000000000^6417 ≤ 43091539281511^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641291023 5000000000 43091539281511 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528258203/1000000000 : ℝ)^8465 ≤ (2154576955467/5000000000000 : ℝ)^6417 := by
    have hnat : (528258203 : ℕ)^8465*5000000000000^6417 ≤ 2154576955467^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528258203 1000000000 2154576955467 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2230375269/10000000000 : ℝ), (2641291023/5000000000 : ℝ), (528258203/1000000000 : ℝ)] ![(13816921601059/100000000000000 : ℝ), (43091539281511/100000000000000 : ℝ), (2154576955467/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2230375269/10000000000 : ℝ)|^8465 ≤ (13816921601059/100000000000000 : ℝ)^6417
        have hw : |(-2230375269/10000000000 : ℝ)|=(2230375269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641291023/5000000000 : ℝ)|^8465 ≤ (43091539281511/100000000000000 : ℝ)^6417
        have hw : |(2641291023/5000000000 : ℝ)|=(2641291023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528258203/1000000000 : ℝ)|^8465 ≤ (2154576955467/5000000000000 : ℝ)^6417
        have hw : |(528258203/1000000000 : ℝ)|=(528258203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361666089/10000000000 : ℝ)*x 0 + (-265648881/1250000000 : ℝ)*x 1 + (528258201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361666089/10000000000 : ℝ)^8465 ≤ (43944565397631/100000000000000 : ℝ)^6417 := by
    have hnat : (5361666089 : ℕ)^8465*100000000000000^6417 ≤ 43944565397631^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361666089 10000000000 43944565397631 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265648881/1250000000 : ℝ)^8465 ≤ (12963895688177/100000000000000 : ℝ)^6417 := by
    have hnat : (265648881 : ℕ)^8465*100000000000000^6417 ≤ 12963895688177^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265648881 1250000000 12963895688177 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528258201/1000000000 : ℝ)^8465 ≤ (21545769447063/50000000000000 : ℝ)^6417 := by
    have hnat : (528258201 : ℕ)^8465*50000000000000^6417 ≤ 21545769447063^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528258201 1000000000 21545769447063 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361666089/10000000000 : ℝ), (-265648881/1250000000 : ℝ), (528258201/1000000000 : ℝ)] ![(43944565397631/100000000000000 : ℝ), (12963895688177/100000000000000 : ℝ), (21545769447063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361666089/10000000000 : ℝ)|^8465 ≤ (43944565397631/100000000000000 : ℝ)^6417
        have hw : |(5361666089/10000000000 : ℝ)|=(5361666089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265648881/1250000000 : ℝ)|^8465 ≤ (12963895688177/100000000000000 : ℝ)^6417
        have hw : |(-265648881/1250000000 : ℝ)|=(265648881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528258201/1000000000 : ℝ)|^8465 ≤ (21545769447063/50000000000000 : ℝ)^6417
        have hw : |(528258201/1000000000 : ℝ)|=(528258201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107233321/200000000 : ℝ)*x 0 + (2641291029/5000000000 : ℝ)*x 1 + (-2125191037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107233321/200000000 : ℝ)^8465 ≤ (1373267655499/3125000000000 : ℝ)^6417 := by
    have hnat : (107233321 : ℕ)^8465*3125000000000^6417 ≤ 1373267655499^6417*200000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107233321 200000000 1373267655499 3125000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641291029/5000000000 : ℝ)^8465 ≤ (538644242633/1250000000000 : ℝ)^6417 := by
    have hnat : (2641291029 : ℕ)^8465*1250000000000^6417 ≤ 538644242633^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641291029 5000000000 538644242633 1250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125191037/10000000000 : ℝ)^8465 ≤ (648194779983/5000000000000 : ℝ)^6417 := by
    have hnat : (2125191037 : ℕ)^8465*5000000000000^6417 ≤ 648194779983^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125191037 10000000000 648194779983 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107233321/200000000 : ℝ), (2641291029/5000000000 : ℝ), (-2125191037/10000000000 : ℝ)] ![(1373267655499/3125000000000 : ℝ), (538644242633/1250000000000 : ℝ), (648194779983/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107233321/200000000 : ℝ)|^8465 ≤ (1373267655499/3125000000000 : ℝ)^6417
        have hw : |(107233321/200000000 : ℝ)|=(107233321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641291029/5000000000 : ℝ)|^8465 ≤ (538644242633/1250000000000 : ℝ)^6417
        have hw : |(2641291029/5000000000 : ℝ)|=(2641291029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125191037/10000000000 : ℝ)|^8465 ≤ (648194779983/5000000000000 : ℝ)^6417
        have hw : |(-2125191037/10000000000 : ℝ)|=(2125191037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2120014057/5000000000 : ℝ)*x 0 + (4402004691/10000000000 : ℝ)*x 1 + (880400931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120014057/5000000000 : ℝ)^8465 ≤ (1289741340491/4000000000000 : ℝ)^6417 := by
    have hnat : (2120014057 : ℕ)^8465*4000000000000^6417 ≤ 1289741340491^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120014057 5000000000 1289741340491 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402004691/10000000000 : ℝ)^8465 ≤ (6775646684269/20000000000000 : ℝ)^6417 := by
    have hnat : (4402004691 : ℕ)^8465*20000000000000^6417 ≤ 6775646684269^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402004691 10000000000 6775646684269 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880400931/2000000000 : ℝ)^8465 ≤ (33878233055861/100000000000000 : ℝ)^6417 := by
    have hnat : (880400931 : ℕ)^8465*100000000000000^6417 ≤ 33878233055861^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880400931 2000000000 33878233055861 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120014057/5000000000 : ℝ), (4402004691/10000000000 : ℝ), (880400931/2000000000 : ℝ)] ![(1289741340491/4000000000000 : ℝ), (6775646684269/20000000000000 : ℝ), (33878233055861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120014057/5000000000 : ℝ)|^8465 ≤ (1289741340491/4000000000000 : ℝ)^6417
        have hw : |(2120014057/5000000000 : ℝ)|=(2120014057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402004691/10000000000 : ℝ)|^8465 ≤ (6775646684269/20000000000000 : ℝ)^6417
        have hw : |(4402004691/10000000000 : ℝ)|=(4402004691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880400931/2000000000 : ℝ)|^8465 ≤ (33878233055861/100000000000000 : ℝ)^6417
        have hw : |(880400931/2000000000 : ℝ)|=(880400931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_8 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-27232569/125000000 : ℝ)*x 0 + (2609954261/5000000000 : ℝ)*x 1 + (5383996323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27232569/125000000 : ℝ)^8465 ≤ (6697717316767/50000000000000 : ℝ)^6417 := by
    have hnat : (27232569 : ℕ)^8465*50000000000000^6417 ≤ 6697717316767^6417*125000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27232569 125000000 6697717316767 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609954261/5000000000 : ℝ)^8465 ≤ (42418408326939/100000000000000 : ℝ)^6417 := by
    have hnat : (2609954261 : ℕ)^8465*100000000000000^6417 ≤ 42418408326939^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609954261 5000000000 42418408326939 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5383996323/10000000000 : ℝ)^8465 ≤ (5523269627627/12500000000000 : ℝ)^6417 := by
    have hnat : (5383996323 : ℕ)^8465*12500000000000^6417 ≤ 5523269627627^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383996323 10000000000 5523269627627 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27232569/125000000 : ℝ), (2609954261/5000000000 : ℝ), (5383996323/10000000000 : ℝ)] ![(6697717316767/50000000000000 : ℝ), (42418408326939/100000000000000 : ℝ), (5523269627627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27232569/125000000 : ℝ)|^8465 ≤ (6697717316767/50000000000000 : ℝ)^6417
        have hw : |(-27232569/125000000 : ℝ)|=(27232569/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609954261/5000000000 : ℝ)|^8465 ≤ (42418408326939/100000000000000 : ℝ)^6417
        have hw : |(2609954261/5000000000 : ℝ)|=(2609954261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5383996323/10000000000 : ℝ)|^8465 ≤ (5523269627627/12500000000000 : ℝ)^6417
        have hw : |(5383996323/10000000000 : ℝ)|=(5383996323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_9 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2645109963/5000000000 : ℝ)*x 0 + (-2084829353/10000000000 : ℝ)*x 1 + (1345999101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645109963/5000000000 : ℝ)^8465 ≤ (21586873601613/50000000000000 : ℝ)^6417 := by
    have hnat : (2645109963 : ℕ)^8465*50000000000000^6417 ≤ 21586873601613^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645109963 5000000000 21586873601613 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084829353/10000000000 : ℝ)^8465 ≤ (395002964979/3125000000000 : ℝ)^6417 := by
    have hnat : (2084829353 : ℕ)^8465*3125000000000^6417 ≤ 395002964979^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084829353 10000000000 395002964979 3125000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345999101/2500000000 : ℝ)^8465 ≤ (44186157897939/100000000000000 : ℝ)^6417 := by
    have hnat : (1345999101 : ℕ)^8465*100000000000000^6417 ≤ 44186157897939^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345999101 2500000000 44186157897939 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645109963/5000000000 : ℝ), (-2084829353/10000000000 : ℝ), (1345999101/2500000000 : ℝ)] ![(21586873601613/50000000000000 : ℝ), (395002964979/3125000000000 : ℝ), (44186157897939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645109963/5000000000 : ℝ)|^8465 ≤ (21586873601613/50000000000000 : ℝ)^6417
        have hw : |(2645109963/5000000000 : ℝ)|=(2645109963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084829353/10000000000 : ℝ)|^8465 ≤ (395002964979/3125000000000 : ℝ)^6417
        have hw : |(-2084829353/10000000000 : ℝ)|=(2084829353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345999101/2500000000 : ℝ)|^8465 ≤ (44186157897939/100000000000000 : ℝ)^6417
        have hw : |(1345999101/2500000000 : ℝ)|=(1345999101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_10 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290220121/10000000000 : ℝ)*x 0 + (1076799249/2000000000 : ℝ)*x 1 + (-2084829307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290220121/10000000000 : ℝ)^8465 ≤ (10793437325633/25000000000000 : ℝ)^6417 := by
    have hnat : (5290220121 : ℕ)^8465*25000000000000^6417 ≤ 10793437325633^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290220121 10000000000 10793437325633 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076799249/2000000000 : ℝ)^8465 ≤ (44186156176571/100000000000000 : ℝ)^6417 := by
    have hnat : (1076799249 : ℕ)^8465*100000000000000^6417 ≤ 44186156176571^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076799249 2000000000 44186156176571 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084829307/10000000000 : ℝ)^8465 ≤ (6320047255713/50000000000000 : ℝ)^6417 := by
    have hnat : (2084829307 : ℕ)^8465*50000000000000^6417 ≤ 6320047255713^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084829307 10000000000 6320047255713 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290220121/10000000000 : ℝ), (1076799249/2000000000 : ℝ), (-2084829307/10000000000 : ℝ)] ![(10793437325633/25000000000000 : ℝ), (44186156176571/100000000000000 : ℝ), (6320047255713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290220121/10000000000 : ℝ)|^8465 ≤ (10793437325633/25000000000000 : ℝ)^6417
        have hw : |(5290220121/10000000000 : ℝ)|=(5290220121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076799249/2000000000 : ℝ)|^8465 ≤ (44186156176571/100000000000000 : ℝ)^6417
        have hw : |(1076799249/2000000000 : ℝ)|=(1076799249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084829307/10000000000 : ℝ)|^8465 ≤ (6320047255713/50000000000000 : ℝ)^6417
        have hw : |(-2084829307/10000000000 : ℝ)|=(2084829307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_11 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4474931187/10000000000 : ℝ)*x 0 + (1071108127/2500000000 : ℝ)*x 1 + (4284432501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474931187/10000000000 : ℝ)^8465 ≤ (34620556313771/100000000000000 : ℝ)^6417 := by
    have hnat : (4474931187 : ℕ)^8465*100000000000000^6417 ≤ 34620556313771^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474931187 10000000000 34620556313771 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071108127/2500000000 : ℝ)^8465 ≤ (32689721866479/100000000000000 : ℝ)^6417 := by
    have hnat : (1071108127 : ℕ)^8465*100000000000000^6417 ≤ 32689721866479^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071108127 2500000000 32689721866479 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4284432501/10000000000 : ℝ)^8465 ≤ (1307588871841/4000000000000 : ℝ)^6417 := by
    have hnat : (4284432501 : ℕ)^8465*4000000000000^6417 ≤ 1307588871841^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284432501 10000000000 1307588871841 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474931187/10000000000 : ℝ), (1071108127/2500000000 : ℝ), (4284432501/10000000000 : ℝ)] ![(34620556313771/100000000000000 : ℝ), (32689721866479/100000000000000 : ℝ), (1307588871841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474931187/10000000000 : ℝ)|^8465 ≤ (34620556313771/100000000000000 : ℝ)^6417
        have hw : |(4474931187/10000000000 : ℝ)|=(4474931187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1071108127/2500000000 : ℝ)|^8465 ≤ (32689721866479/100000000000000 : ℝ)^6417
        have hw : |(1071108127/2500000000 : ℝ)|=(1071108127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4284432501/10000000000 : ℝ)|^8465 ≤ (1307588871841/4000000000000 : ℝ)^6417
        have hw : |(4284432501/10000000000 : ℝ)|=(4284432501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_12 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-508869597/2500000000 : ℝ)*x 0 + (2717934089/5000000000 : ℝ)*x 1 + (5274492837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508869597/2500000000 : ℝ)^8465 ≤ (12246890951989/100000000000000 : ℝ)^6417 := by
    have hnat : (508869597 : ℕ)^8465*100000000000000^6417 ≤ 12246890951989^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508869597 2500000000 12246890951989 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717934089/5000000000 : ℝ)^8465 ≤ (44748594057709/100000000000000 : ℝ)^6417 := by
    have hnat : (2717934089 : ℕ)^8465*100000000000000^6417 ≤ 44748594057709^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717934089 5000000000 44748594057709 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274492837/10000000000 : ℝ)^8465 ≤ (43004514976639/100000000000000 : ℝ)^6417 := by
    have hnat : (5274492837 : ℕ)^8465*100000000000000^6417 ≤ 43004514976639^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274492837 10000000000 43004514976639 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508869597/2500000000 : ℝ), (2717934089/5000000000 : ℝ), (5274492837/10000000000 : ℝ)] ![(12246890951989/100000000000000 : ℝ), (44748594057709/100000000000000 : ℝ), (43004514976639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508869597/2500000000 : ℝ)|^8465 ≤ (12246890951989/100000000000000 : ℝ)^6417
        have hw : |(-508869597/2500000000 : ℝ)|=(508869597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717934089/5000000000 : ℝ)|^8465 ≤ (44748594057709/100000000000000 : ℝ)^6417
        have hw : |(2717934089/5000000000 : ℝ)|=(2717934089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274492837/10000000000 : ℝ)|^8465 ≤ (43004514976639/100000000000000 : ℝ)^6417
        have hw : |(5274492837/10000000000 : ℝ)|=(5274492837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_13 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341840749/2500000000 : ℝ)*x 0 + (-2128349773/10000000000 : ℝ)*x 1 + (1054898477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341840749/2500000000 : ℝ)^8465 ≤ (11001542497039/25000000000000 : ℝ)^6417 := by
    have hnat : (1341840749 : ℕ)^8465*25000000000000^6417 ≤ 11001542497039^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341840749 2500000000 11001542497039 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128349773/10000000000 : ℝ)^8465 ≤ (2597863977103/20000000000000 : ℝ)^6417 := by
    have hnat : (2128349773 : ℕ)^8465*20000000000000^6417 ≤ 2597863977103^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128349773 10000000000 2597863977103 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054898477/2000000000 : ℝ)^8465 ≤ (43004510115179/100000000000000 : ℝ)^6417 := by
    have hnat : (1054898477 : ℕ)^8465*100000000000000^6417 ≤ 43004510115179^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054898477 2000000000 43004510115179 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341840749/2500000000 : ℝ), (-2128349773/10000000000 : ℝ), (1054898477/2000000000 : ℝ)] ![(11001542497039/25000000000000 : ℝ), (2597863977103/20000000000000 : ℝ), (43004510115179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341840749/2500000000 : ℝ)|^8465 ≤ (11001542497039/25000000000000 : ℝ)^6417
        have hw : |(1341840749/2500000000 : ℝ)|=(1341840749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128349773/10000000000 : ℝ)|^8465 ≤ (2597863977103/20000000000000 : ℝ)^6417
        have hw : |(-2128349773/10000000000 : ℝ)|=(2128349773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054898477/2000000000 : ℝ)|^8465 ≤ (43004510115179/100000000000000 : ℝ)^6417
        have hw : |(1054898477/2000000000 : ℝ)|=(1054898477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_14 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167730091/312500000 : ℝ)*x 0 + (1318623139/2500000000 : ℝ)*x 1 + (-266043707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167730091/312500000 : ℝ)^8465 ≤ (11001542269913/25000000000000 : ℝ)^6417 := by
    have hnat : (167730091 : ℕ)^8465*25000000000000^6417 ≤ 11001542269913^6417*312500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167730091 312500000 11001542269913 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318623139/2500000000 : ℝ)^8465 ≤ (1075112798859/2500000000000 : ℝ)^6417 := by
    have hnat : (1318623139 : ℕ)^8465*2500000000000^6417 ≤ 1075112798859^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318623139 2500000000 1075112798859 2500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266043707/1250000000 : ℝ)^8465 ≤ (12989318943573/100000000000000 : ℝ)^6417 := by
    have hnat : (266043707 : ℕ)^8465*100000000000000^6417 ≤ 12989318943573^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266043707 1250000000 12989318943573 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167730091/312500000 : ℝ), (1318623139/2500000000 : ℝ), (-266043707/1250000000 : ℝ)] ![(11001542269913/25000000000000 : ℝ), (1075112798859/2500000000000 : ℝ), (12989318943573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167730091/312500000 : ℝ)|^8465 ≤ (11001542269913/25000000000000 : ℝ)^6417
        have hw : |(167730091/312500000 : ℝ)|=(167730091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318623139/2500000000 : ℝ)|^8465 ≤ (1075112798859/2500000000000 : ℝ)^6417
        have hw : |(1318623139/2500000000 : ℝ)|=(1318623139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266043707/1250000000 : ℝ)|^8465 ≤ (12989318943573/100000000000000 : ℝ)^6417
        have hw : |(-266043707/1250000000 : ℝ)|=(266043707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_box_15 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1055259133/2500000000 : ℝ)*x 0 + (220568879/500000000 : ℝ)*x 1 + (4411377673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055259133/2500000000 : ℝ)^8465 ≤ (8013288619937/25000000000000 : ℝ)^6417 := by
    have hnat : (1055259133 : ℕ)^8465*25000000000000^6417 ≤ 8013288619937^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055259133 2500000000 8013288619937 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220568879/500000000 : ℝ)^8465 ≤ (1061669446239/3125000000000 : ℝ)^6417 := by
    have hnat : (220568879 : ℕ)^8465*3125000000000^6417 ≤ 1061669446239^6417*500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220568879 500000000 1061669446239 3125000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4411377673/10000000000 : ℝ)^8465 ≤ (16986711612227/50000000000000 : ℝ)^6417 := by
    have hnat : (4411377673 : ℕ)^8465*50000000000000^6417 ≤ 16986711612227^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411377673 10000000000 16986711612227 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055259133/2500000000 : ℝ), (220568879/500000000 : ℝ), (4411377673/10000000000 : ℝ)] ![(8013288619937/25000000000000 : ℝ), (1061669446239/3125000000000 : ℝ), (16986711612227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055259133/2500000000 : ℝ)|^8465 ≤ (8013288619937/25000000000000 : ℝ)^6417
        have hw : |(1055259133/2500000000 : ℝ)|=(1055259133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220568879/500000000 : ℝ)|^8465 ≤ (1061669446239/3125000000000 : ℝ)^6417
        have hw : |(220568879/500000000 : ℝ)|=(220568879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4411377673/10000000000 : ℝ)|^8465 ≤ (16986711612227/50000000000000 : ℝ)^6417
        have hw : |(4411377673/10000000000 : ℝ)|=(4411377673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62253/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29701/50000 : ℝ) ∧ (80197/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83411/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2303/20000 : ℝ) ^ (529/128 : ℝ) ≤ (13194103499835267/100000000000000000000 : ℝ) := by
    have hpowers : (2303/20000 : ℝ)^529 ≤ (13194103499835267/100000000000000000000 : ℝ)^128 := by
      have hnat : (2303 : ℕ)^529*100000000000000000000^128 ≤ 13194103499835267^128*20000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2303 20000 13194103499835267 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2303/20000 : ℝ)) (X := (13194103499835267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (529/128 : ℝ) ≤ (6128145725156683/20000000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^529 ≤ (6128145725156683/20000000000000000000 : ℝ)^128 := by
      have hnat : (14119 : ℕ)^529*20000000000000000000^128 ≤ 6128145725156683^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 6128145725156683 20000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (6128145725156683/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013194103499835267/50000000000000000000 : ℝ) ≤ (10000638440968959/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50013194103499835267/50000000000000000000 : ℝ)^128 ≤ (10000638440968959/10000000000000000 : ℝ)^529 := by
      have hnat : (50013194103499835267 : ℕ)^128*10000000000000000^529 ≤ 10000638440968959^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013194103499835267 50000000000000000000 10000638440968959 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000638440968959/10000000000000000 : ℝ)) (X := (50013194103499835267/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021917416062809341/50000000000000000000 : ℝ) ≤ (400042419104387/400000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50021917416062809341/50000000000000000000 : ℝ)^128 ≤ (400042419104387/400000000000000 : ℝ)^529 := by
      have hnat : (50021917416062809341 : ℕ)^128*400000000000000^529 ≤ 400042419104387^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021917416062809341 50000000000000000000 400042419104387 400000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400042419104387/400000000000000 : ℝ)) (X := (50021917416062809341/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006128145725156683/10000000000000000000 : ℝ) ≤ (10001482514250391/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (10006128145725156683/10000000000000000000 : ℝ)^128 ≤ (10001482514250391/10000000000000000 : ℝ)^529 := by
      have hnat : (10006128145725156683 : ℕ)^128*10000000000000000^529 ≤ 10001482514250391^529*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006128145725156683 10000000000000000000 10001482514250391 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001482514250391/10000000000000000 : ℝ)) (X := (10006128145725156683/10000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13194103499835267/100000000000000000000 : ℝ) ≤ ((929712249873124277/930000000000000000 : ℝ)+2*(105509160179/65100000000000 : ℝ)*(2303/20000 : ℝ))^(529/128 : ℝ) := by
    rw [show (929712249873124277/930000000000000000 : ℝ)+2*(105509160179/65100000000000 : ℝ)*(2303/20000 : ℝ)=(10000638440968959/10000000000000000 : ℝ) by norm_num, show 1+2*(13194103499835267/100000000000000000000 : ℝ)=(50013194103499835267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6128145725156683/20000000000000000000 : ℝ)+(13194103499835267/100000000000000000000 : ℝ) ≤ ((929712249873124277/930000000000000000 : ℝ)+(105509160179/65100000000000 : ℝ)*((14119/100000 : ℝ)+(2303/20000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (929712249873124277/930000000000000000 : ℝ)+(105509160179/65100000000000 : ℝ)*((14119/100000 : ℝ)+(2303/20000 : ℝ))=(400042419104387/400000000000000 : ℝ) by norm_num, show 1+(6128145725156683/20000000000000000000 : ℝ)+(13194103499835267/100000000000000000000 : ℝ)=(50021917416062809341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6128145725156683/20000000000000000000 : ℝ) ≤ ((929712249873124277/930000000000000000 : ℝ)+2*(105509160179/65100000000000 : ℝ)*(14119/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (929712249873124277/930000000000000000 : ℝ)+2*(105509160179/65100000000000 : ℝ)*(14119/100000 : ℝ)=(10001482514250391/10000000000000000 : ℝ) by norm_num, show 1+2*(6128145725156683/20000000000000000000 : ℝ)=(10006128145725156683/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (929712249873124277/930000000000000000 : ℝ)*(X 1 0+X 2 0)+(105509160179/65100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (929712249873124277/930000000000000000 : ℝ)) (alpha := (105509160179/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (929712249873124277/930000000000000000 : ℝ)*(X 0 1+X 2 1)+(105509160179/65100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (929712249873124277/930000000000000000 : ℝ)) (alpha := (105509160179/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (929712249873124277/930000000000000000 : ℝ)*(X 0 2+X 1 2)+(105509160179/65100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (929712249873124277/930000000000000000 : ℝ)) (alpha := (105509160179/65100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-198346601/1000000000 : ℝ)*X 0 0+(5374383591/10000000000 : ℝ)*X 0 1+(5374383739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059398981/2000000000 : ℝ)*X 1 0+(-2088715137/10000000000 : ℝ)*X 1 1+(2687191857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296994599/10000000000 : ℝ)*X 2 0+(1343595953/2500000000 : ℝ)*X 2 1+(-2088715417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1113228069/2500000000 : ℝ)*X 0 0+(4295582479/10000000000 : ℝ)*X 0 1+(53694781/125000000 : ℝ)*X 0 2+(1113228069/2500000000 : ℝ)*X 1 0+(4295582479/10000000000 : ℝ)*X 1 1+(53694781/125000000 : ℝ)*X 1 2+(1113228069/2500000000 : ℝ)*X 2 0+(4295582479/10000000000 : ℝ)*X 2 1+(53694781/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2230375269/10000000000 : ℝ)*X 0 0+(2641291023/5000000000 : ℝ)*X 0 1+(528258203/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361666089/10000000000 : ℝ)*X 1 0+(-265648881/1250000000 : ℝ)*X 1 1+(528258201/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((107233321/200000000 : ℝ)*X 2 0+(2641291029/5000000000 : ℝ)*X 2 1+(-2125191037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120014057/5000000000 : ℝ)*X 0 0+(4402004691/10000000000 : ℝ)*X 0 1+(880400931/2000000000 : ℝ)*X 0 2+(2120014057/5000000000 : ℝ)*X 1 0+(4402004691/10000000000 : ℝ)*X 1 1+(880400931/2000000000 : ℝ)*X 1 2+(2120014057/5000000000 : ℝ)*X 2 0+(4402004691/10000000000 : ℝ)*X 2 1+(880400931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-27232569/125000000 : ℝ)*X 0 0+(2609954261/5000000000 : ℝ)*X 0 1+(5383996323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2645109963/5000000000 : ℝ)*X 1 0+(-2084829353/10000000000 : ℝ)*X 1 1+(1345999101/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290220121/10000000000 : ℝ)*X 2 0+(1076799249/2000000000 : ℝ)*X 2 1+(-2084829307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4474931187/10000000000 : ℝ)*X 0 0+(1071108127/2500000000 : ℝ)*X 0 1+(4284432501/10000000000 : ℝ)*X 0 2+(4474931187/10000000000 : ℝ)*X 1 0+(1071108127/2500000000 : ℝ)*X 1 1+(4284432501/10000000000 : ℝ)*X 1 2+(4474931187/10000000000 : ℝ)*X 2 0+(1071108127/2500000000 : ℝ)*X 2 1+(4284432501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-508869597/2500000000 : ℝ)*X 0 0+(2717934089/5000000000 : ℝ)*X 0 1+(5274492837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1341840749/2500000000 : ℝ)*X 1 0+(-2128349773/10000000000 : ℝ)*X 1 1+(1054898477/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((167730091/312500000 : ℝ)*X 2 0+(1318623139/2500000000 : ℝ)*X 2 1+(-266043707/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1055259133/2500000000 : ℝ)*X 0 0+(220568879/500000000 : ℝ)*X 0 1+(4411377673/10000000000 : ℝ)*X 0 2+(1055259133/2500000000 : ℝ)*X 1 0+(220568879/500000000 : ℝ)*X 1 1+(4411377673/10000000000 : ℝ)*X 1 2+(1055259133/2500000000 : ℝ)*X 2 0+(220568879/500000000 : ℝ)*X 2 1+(4411377673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62253/100000 : ℝ) ≤ (-8442684388416304205000416216087/13562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2303153/20000000000000 : ℝ)*(lower0) + (4978089/25000000000000 : ℝ)*(lower2) + (6152087/25000000000000 : ℝ)*(lower4) + (662593/50000000000000 : ℝ)*(lower5) + (503484594614311/12500000000000 : ℝ)*(major0) + (503484594614311/12500000000000 : ℝ)*(major1) + (503484594614311/12500000000000 : ℝ)*(major2) + (227316889/10000000000000 : ℝ)*(sp1) + (542686936622591/10000000000000 : ℝ)*(sp4) + (5426868080525017/100000000000000 : ℝ)*(sp5) + (339179203144889/6250000000000 : ℝ)*(sp6) + (132481661464623/5000000000000 : ℝ)*(sp7) + (987467997/100000000000000 : ℝ)*(sp8) + (3103375683/100000000000000 : ℝ)*(sp14) + (132481661464623/5000000000000 : ℝ)*(f.failure) + (5426870353693907/100000000000000 : ℝ)*(f.sum) + (1211631777401/1627500000000000000000000000 : ℝ)*base65 + (194976302335247029/81375000000000000000000000000000 : ℝ)*base67 + (802158999644372029/81375000000000000000000000000000 : ℝ)*base69 + (1295836649322872029/81375000000000000000000000000000 : ℝ)*base71 + (3105046533859/1627500000000000000000000000 : ℝ)*base74 + (661215115438247029/81375000000000000000000000000000 : ℝ)*base75 + (1071696524749997029/81375000000000000000000000000000 : ℝ)*base77 + (1036462283791997029/81375000000000000000000000000000 : ℝ)*base79 + (1650200812367/813750000000000000000000000 : ℝ)*base82 + (293653/500000000000000000000 : ℝ)*base90 + (293653/500000000000000000000 : ℝ)*base92 + (293653/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29701/50000 : ℝ) ≤ (9207653075794118413909607190567/15500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18968451/20000000000000 : ℝ)*(lower0) + (187060133/100000000000000 : ℝ)*(upper2) + (33298117/100000000000000 : ℝ)*(lower4) + (2840881/10000000000000 : ℝ)*(lower5) + (4094176513250229/100000000000000 : ℝ)*(major0) + (4094176513250229/100000000000000 : ℝ)*(major1) + (4094176513250229/100000000000000 : ℝ)*(major2) + (5475295958990029/100000000000000 : ℝ)*(sp0) + (547529666798293/10000000000000 : ℝ)*(sp1) + (684413104314233/12500000000000 : ℝ)*(sp2) + (42081901262031/1562500000000 : ℝ)*(sp3) + (4083265467/50000000000000 : ℝ)*(sp5) + (510675253/10000000000000 : ℝ)*(sp7) + (1775104767/20000000000000 : ℝ)*(sp12) + (1346623393761257/50000000000000 : ℝ)*(f.failure) + (684413104314233/12500000000000 : ℝ)*(f.sum) + (453251119199/155000000000000000000000000 : ℝ)*base66 + (137300874610669811/31000000000000000000000000000000 : ℝ)*base67 + (57796710319669811/31000000000000000000000000000000 : ℝ)*base69 + (57786944184330189/31000000000000000000000000000000 : ℝ)*base72 + (1797290199351/155000000000000000000000000 : ℝ)*base73 + (104267911734330189/31000000000000000000000000000000 : ℝ)*base76 + (67318151255669811/31000000000000000000000000000000 : ℝ)*base77 + (105558957841669811/31000000000000000000000000000000 : ℝ)*base79 + (293615381361/155000000000000000000000000 : ℝ)*base81 + (32759027/5000000000000000000000 : ℝ)*base90 + (32759027/5000000000000000000000 : ℝ)*base92 + (32759027/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80197/100000 : ℝ) ≤ (43508244707124299479466209146447/54250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11827789/20000000000000 : ℝ)*(upper0) + (4267283/25000000000000 : ℝ)*(upper1) + (45349417/50000000000000 : ℝ)*(upper4) + (2280265244926827/50000000000000 : ℝ)*(major0) + (2280265244926827/50000000000000 : ℝ)*(major1) + (2280265244926827/50000000000000 : ℝ)*(major2) + (101803732069/100000000000000 : ℝ)*(sp1) + (15068229009/25000000000000 : ℝ)*(sp2) + (34530712941/100000000000000 : ℝ)*(sp3) + (3098950889/100000000000000 : ℝ)*(sp4) + (609429916766107/10000000000000 : ℝ)*(sp8) + (6094200462879891/100000000000000 : ℝ)*(sp9) + (6094241993695923/100000000000000 : ℝ)*(sp10) + (749997751477761/25000000000000 : ℝ)*(sp11) + (187501596038999/6250000000000 : ℝ)*(f.failure) + (152357556665299/2500000000000 : ℝ)*(f.sum) + (10113126159233/1085000000000000000000000000 : ℝ)*base66 + (112480393503917851/108500000000000000000000000000000 : ℝ)*base67 + (169862953532417851/108500000000000000000000000000000 : ℝ)*base69 + (453902450598917851/108500000000000000000000000000000 : ℝ)*base71 + (3205026326753/1085000000000000000000000000 : ℝ)*base74 + (395082002042582149/108500000000000000000000000000000 : ℝ)*base76 + (1160048689242917851/108500000000000000000000000000000 : ℝ)*base77 + (457105647726582149/108500000000000000000000000000000 : ℝ)*base80 + (8972519852813/1085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6345389/625000000000000000000 : ℝ)*base90 + (6345389/625000000000000000000 : ℝ)*base92 + (6345389/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83411/100000 : ℝ) ≤ (-226245484273593597289351691/271250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8187557/50000000000000 : ℝ)*(upper1) + (53204781/50000000000000 : ℝ)*(upper3) + (48634227/25000000000000 : ℝ)*(upper5) + (35908155915463/781250000000 : ℝ)*(major0) + (35908155915463/781250000000 : ℝ)*(major1) + (35908155915463/781250000000 : ℝ)*(major2) + (2681829573/6250000000000 : ℝ)*(sp4) + (250220923481/50000000000000 : ℝ)*(sp5) + (409074646443/100000000000000 : ℝ)*(sp6) + (310489137493/100000000000000 : ℝ)*(sp7) + (3098364561925453/50000000000000 : ℝ)*(sp12) + (774533948909639/12500000000000 : ℝ)*(sp13) + (6196362958477631/100000000000000 : ℝ)*(sp14) + (3023208216585259/100000000000000 : ℝ)*(sp15) + (23621239888459/781250000000 : ℝ)*(f.failure) + (3098386016562037/50000000000000 : ℝ)*(f.sum) + (5283906670297/1627500000000000000000000000 : ℝ)*base66 + (19016862086369611/10171875000000000000000000000000 : ℝ)*base68 + (148263454832166757/5085937500000000000000000000000 : ℝ)*base69 + (9621329676104257/5085937500000000000000000000000 : ℝ)*base71 + (197132253149/3255000000000000000000000000 : ℝ)*base74 + (40587223990471309/2542968750000000000000000000000 : ℝ)*base76 + (549225330385507/5085937500000000000000000000000 : ℝ)*base77 + (12497946783775861/10171875000000000000000000000000 : ℝ)*base80 + (90822124290031/3255000000000000000000000000 : ℝ)*base81 + (45449/78125000000000000000 : ℝ)*base90 + (45449/78125000000000000000 : ℝ)*base92 + (45449/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1271_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83411/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1271_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1271_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83411/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1271_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1271_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83411/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
