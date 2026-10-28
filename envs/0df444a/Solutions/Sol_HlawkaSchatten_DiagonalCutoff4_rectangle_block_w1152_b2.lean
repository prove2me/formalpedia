-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:14.251204+00:00
-- url     : https://prove2.me/submissions/f0f58aba-1183-4796-a126-4e315cc6f1db

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
theorem support_rectangle_w1152_s6_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43241667/200000000 : ℝ)*x 0 + (2696590399/5000000000 : ℝ)*x 1 + (2632795767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43241667/200000000 : ℝ)^8345 ≤ (6569316388561/50000000000000 : ℝ)^6297 := by
    have hnat : (43241667 : ℕ)^8345*50000000000000^6297 ≤ 6569316388561^6297*200000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43241667 200000000 6569316388561 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696590399/5000000000 : ℝ)^8345 ≤ (44119622283471/100000000000000 : ℝ)^6297 := by
    have hnat : (2696590399 : ℕ)^8345*100000000000000^6297 ≤ 44119622283471^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696590399 5000000000 44119622283471 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632795767/5000000000 : ℝ)^8345 ≤ (10685436228057/25000000000000 : ℝ)^6297 := by
    have hnat : (2632795767 : ℕ)^8345*25000000000000^6297 ≤ 10685436228057^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632795767 5000000000 10685436228057 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43241667/200000000 : ℝ), (2696590399/5000000000 : ℝ), (2632795767/5000000000 : ℝ)] ![(6569316388561/50000000000000 : ℝ), (44119622283471/100000000000000 : ℝ), (10685436228057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43241667/200000000 : ℝ)|^8345 ≤ (6569316388561/50000000000000 : ℝ)^6297
        have hw : |(-43241667/200000000 : ℝ)|=(43241667/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696590399/5000000000 : ℝ)|^8345 ≤ (44119622283471/100000000000000 : ℝ)^6297
        have hw : |(2696590399/5000000000 : ℝ)|=(2696590399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632795767/5000000000 : ℝ)|^8345 ≤ (10685436228057/25000000000000 : ℝ)^6297
        have hw : |(2632795767/5000000000 : ℝ)|=(2632795767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344803069/10000000000 : ℝ)*x 0 + (-278350147/1250000000 : ℝ)*x 1 + (5265591591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344803069/10000000000 : ℝ)^8345 ≤ (2724744607349/6250000000000 : ℝ)^6297 := by
    have hnat : (5344803069 : ℕ)^8345*6250000000000^6297 ≤ 2724744607349^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344803069 10000000000 2724744607349 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278350147/1250000000 : ℝ)^8345 ≤ (6831170370367/50000000000000 : ℝ)^6297 := by
    have hnat : (278350147 : ℕ)^8345*50000000000000^6297 ≤ 6831170370367^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278350147 1250000000 6831170370367 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265591591/10000000000 : ℝ)^8345 ≤ (21370872762693/50000000000000 : ℝ)^6297 := by
    have hnat : (5265591591 : ℕ)^8345*50000000000000^6297 ≤ 21370872762693^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265591591 10000000000 21370872762693 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344803069/10000000000 : ℝ), (-278350147/1250000000 : ℝ), (5265591591/10000000000 : ℝ)] ![(2724744607349/6250000000000 : ℝ), (6831170370367/50000000000000 : ℝ), (21370872762693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344803069/10000000000 : ℝ)|^8345 ≤ (2724744607349/6250000000000 : ℝ)^6297
        have hw : |(5344803069/10000000000 : ℝ)|=(5344803069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278350147/1250000000 : ℝ)|^8345 ≤ (6831170370367/50000000000000 : ℝ)^6297
        have hw : |(-278350147/1250000000 : ℝ)|=(278350147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265591591/10000000000 : ℝ)|^8345 ≤ (21370872762693/50000000000000 : ℝ)^6297
        have hw : |(5265591591/10000000000 : ℝ)|=(5265591591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344803337/10000000000 : ℝ)*x 0 + (42124731/80000000 : ℝ)*x 1 + (-445360221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344803337/10000000000 : ℝ)^8345 ≤ (43595916614537/100000000000000 : ℝ)^6297 := by
    have hnat : (5344803337 : ℕ)^8345*100000000000000^6297 ≤ 43595916614537^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344803337 10000000000 43595916614537 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42124731/80000000 : ℝ)^8345 ≤ (42741743201839/100000000000000 : ℝ)^6297 := by
    have hnat : (42124731 : ℕ)^8345*100000000000000^6297 ≤ 42741743201839^6297*80000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42124731 80000000 42741743201839 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445360221/2000000000 : ℝ)^8345 ≤ (13662340163443/100000000000000 : ℝ)^6297 := by
    have hnat : (445360221 : ℕ)^8345*100000000000000^6297 ≤ 13662340163443^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445360221 2000000000 13662340163443 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344803337/10000000000 : ℝ), (42124731/80000000 : ℝ), (-445360221/2000000000 : ℝ)] ![(43595916614537/100000000000000 : ℝ), (42741743201839/100000000000000 : ℝ), (13662340163443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344803337/10000000000 : ℝ)|^8345 ≤ (43595916614537/100000000000000 : ℝ)^6297
        have hw : |(5344803337/10000000000 : ℝ)|=(5344803337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42124731/80000000 : ℝ)|^8345 ≤ (42741743201839/100000000000000 : ℝ)^6297
        have hw : |(42124731/80000000 : ℝ)|=(42124731/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445360221/2000000000 : ℝ)|^8345 ≤ (13662340163443/100000000000000 : ℝ)^6297
        have hw : |(-445360221/2000000000 : ℝ)|=(445360221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181625191/5000000000 : ℝ)*x 0 + (4237922617/10000000000 : ℝ)*x 1 + (224612831/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181625191/5000000000 : ℝ)^8345 ≤ (33316859627169/100000000000000 : ℝ)^6297 := by
    have hnat : (2181625191 : ℕ)^8345*100000000000000^6297 ≤ 33316859627169^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181625191 5000000000 33316859627169 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237922617/10000000000 : ℝ)^8345 ≤ (32054604259327/100000000000000 : ℝ)^6297 := by
    have hnat : (4237922617 : ℕ)^8345*100000000000000^6297 ≤ 32054604259327^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237922617 10000000000 32054604259327 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224612831/500000000 : ℝ)^8345 ≤ (34628536091957/100000000000000 : ℝ)^6297 := by
    have hnat : (224612831 : ℕ)^8345*100000000000000^6297 ≤ 34628536091957^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224612831 500000000 34628536091957 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181625191/5000000000 : ℝ), (4237922617/10000000000 : ℝ), (224612831/500000000 : ℝ)] ![(33316859627169/100000000000000 : ℝ), (32054604259327/100000000000000 : ℝ), (34628536091957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181625191/5000000000 : ℝ)|^8345 ≤ (33316859627169/100000000000000 : ℝ)^6297
        have hw : |(2181625191/5000000000 : ℝ)|=(2181625191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237922617/10000000000 : ℝ)|^8345 ≤ (32054604259327/100000000000000 : ℝ)^6297
        have hw : |(4237922617/10000000000 : ℝ)|=(4237922617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224612831/500000000 : ℝ)|^8345 ≤ (34628536091957/100000000000000 : ℝ)^6297
        have hw : |(224612831/500000000 : ℝ)|=(224612831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135130531/625000000 : ℝ)*x 0 + (5265914087/10000000000 : ℝ)*x 1 + (5392856919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135130531/625000000 : ℝ)^8345 ≤ (13138674219087/100000000000000 : ℝ)^6297 := by
    have hnat : (135130531 : ℕ)^8345*100000000000000^6297 ≤ 13138674219087^6297*625000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135130531 625000000 13138674219087 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265914087/10000000000 : ℝ)^8345 ≤ (21372607350913/50000000000000 : ℝ)^6297 := by
    have hnat : (5265914087 : ℕ)^8345*50000000000000^6297 ≤ 21372607350913^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265914087 10000000000 21372607350913 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392856919/10000000000 : ℝ)^8345 ≤ (44116111063789/100000000000000 : ℝ)^6297 := by
    have hnat : (5392856919 : ℕ)^8345*100000000000000^6297 ≤ 44116111063789^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392856919 10000000000 44116111063789 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135130531/625000000 : ℝ), (5265914087/10000000000 : ℝ), (5392856919/10000000000 : ℝ)] ![(13138674219087/100000000000000 : ℝ), (21372607350913/50000000000000 : ℝ), (44116111063789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135130531/625000000 : ℝ)|^8345 ≤ (13138674219087/100000000000000 : ℝ)^6297
        have hw : |(-135130531/625000000 : ℝ)|=(135130531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265914087/10000000000 : ℝ)|^8345 ≤ (21372607350913/50000000000000 : ℝ)^6297
        have hw : |(5265914087/10000000000 : ℝ)|=(5265914087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392856919/10000000000 : ℝ)|^8345 ≤ (44116111063789/100000000000000 : ℝ)^6297
        have hw : |(5392856919/10000000000 : ℝ)|=(5392856919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664056771/1250000000 : ℝ)*x 0 + (-1049767371/5000000000 : ℝ)*x 1 + (5392857607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664056771/1250000000 : ℝ)^8345 ≤ (21623291000813/50000000000000 : ℝ)^6297 := by
    have hnat : (664056771 : ℕ)^8345*50000000000000^6297 ≤ 21623291000813^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664056771 1250000000 21623291000813 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049767371/5000000000 : ℝ)^8345 ≤ (12637299460821/100000000000000 : ℝ)^6297 := by
    have hnat : (1049767371 : ℕ)^8345*100000000000000^6297 ≤ 12637299460821^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049767371 5000000000 12637299460821 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392857607/10000000000 : ℝ)^8345 ≤ (1764644740897/4000000000000 : ℝ)^6297 := by
    have hnat : (5392857607 : ℕ)^8345*4000000000000^6297 ≤ 1764644740897^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392857607 10000000000 1764644740897 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664056771/1250000000 : ℝ), (-1049767371/5000000000 : ℝ), (5392857607/10000000000 : ℝ)] ![(21623291000813/50000000000000 : ℝ), (12637299460821/100000000000000 : ℝ), (1764644740897/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664056771/1250000000 : ℝ)|^8345 ≤ (21623291000813/50000000000000 : ℝ)^6297
        have hw : |(664056771/1250000000 : ℝ)|=(664056771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049767371/5000000000 : ℝ)|^8345 ≤ (12637299460821/100000000000000 : ℝ)^6297
        have hw : |(-1049767371/5000000000 : ℝ)|=(1049767371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392857607/10000000000 : ℝ)|^8345 ≤ (1764644740897/4000000000000 : ℝ)^6297
        have hw : |(5392857607/10000000000 : ℝ)|=(5392857607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062490843/2000000000 : ℝ)*x 0 + (33705357/62500000 : ℝ)*x 1 + (-2099535341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062490843/2000000000 : ℝ)^8345 ≤ (337863925849/781250000000 : ℝ)^6297 := by
    have hnat : (1062490843 : ℕ)^8345*781250000000^6297 ≤ 337863925849^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062490843 2000000000 337863925849 781250000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33705357/62500000 : ℝ)^8345 ≤ (22058056621419/50000000000000 : ℝ)^6297 := by
    have hnat : (33705357 : ℕ)^8345*50000000000000^6297 ≤ 22058056621419^6297*62500000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33705357 62500000 22058056621419 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099535341/10000000000 : ℝ)^8345 ≤ (12637304238871/100000000000000 : ℝ)^6297 := by
    have hnat : (2099535341 : ℕ)^8345*100000000000000^6297 ≤ 12637304238871^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099535341 10000000000 12637304238871 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062490843/2000000000 : ℝ), (33705357/62500000 : ℝ), (-2099535341/10000000000 : ℝ)] ![(337863925849/781250000000 : ℝ), (22058056621419/50000000000000 : ℝ), (12637304238871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062490843/2000000000 : ℝ)|^8345 ≤ (337863925849/781250000000 : ℝ)^6297
        have hw : |(1062490843/2000000000 : ℝ)|=(1062490843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33705357/62500000 : ℝ)|^8345 ≤ (22058056621419/50000000000000 : ℝ)^6297
        have hw : |(33705357/62500000 : ℝ)|=(33705357/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099535341/10000000000 : ℝ)|^8345 ≤ (12637304238871/100000000000000 : ℝ)^6297
        have hw : |(-2099535341/10000000000 : ℝ)|=(2099535341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s6_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363260427/10000000000 : ℝ)*x 0 + (1122903567/2500000000 : ℝ)*x 1 + (423856709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363260427/10000000000 : ℝ)^8345 ≤ (33316961274663/100000000000000 : ℝ)^6297 := by
    have hnat : (4363260427 : ℕ)^8345*100000000000000^6297 ≤ 33316961274663^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363260427 10000000000 33316961274663 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122903567/2500000000 : ℝ)^8345 ≤ (34621974258489/100000000000000 : ℝ)^6297 := by
    have hnat : (1122903567 : ℕ)^8345*100000000000000^6297 ≤ 34621974258489^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122903567 2500000000 34621974258489 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423856709/1000000000 : ℝ)^8345 ≤ (62619266509/195312500000 : ℝ)^6297 := by
    have hnat : (423856709 : ℕ)^8345*195312500000^6297 ≤ 62619266509^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423856709 1000000000 62619266509 195312500000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363260427/10000000000 : ℝ), (1122903567/2500000000 : ℝ), (423856709/1000000000 : ℝ)] ![(33316961274663/100000000000000 : ℝ), (34621974258489/100000000000000 : ℝ), (62619266509/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363260427/10000000000 : ℝ)|^8345 ≤ (33316961274663/100000000000000 : ℝ)^6297
        have hw : |(4363260427/10000000000 : ℝ)|=(4363260427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122903567/2500000000 : ℝ)|^8345 ≤ (34621974258489/100000000000000 : ℝ)^6297
        have hw : |(1122903567/2500000000 : ℝ)|=(1122903567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423856709/1000000000 : ℝ)|^8345 ≤ (62619266509/195312500000 : ℝ)^6297
        have hw : |(423856709/1000000000 : ℝ)|=(423856709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1133/10000 : ℝ) ^ (1043/256 : ℝ) ≤ (7009640900649179/50000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^1043 ≤ (7009640900649179/50000000000000000000 : ℝ)^256 := by
      have hnat : (1133 : ℕ)^1043*50000000000000000000^256 ≤ 7009640900649179^256*10000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 7009640900649179 50000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (7009640900649179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (1043/256 : ℝ) ≤ (8526953925677311/25000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^1043 ≤ (8526953925677311/25000000000000000000 : ℝ)^256 := by
      have hnat : (14093 : ℕ)^1043*25000000000000000000^256 ≤ 8526953925677311^256*100000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 8526953925677311 25000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (8526953925677311/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007009640900649179/25000000000000000000 : ℝ) ≤ (5000344061031129/5000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (25007009640900649179/25000000000000000000 : ℝ)^256 ≤ (5000344061031129/5000000000000000 : ℝ)^1043 := by
      have hnat : (25007009640900649179 : ℕ)^256*5000000000000000^1043 ≤ 5000344061031129^1043*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007009640900649179 25000000000000000000 5000344061031129 5000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344061031129/5000000000000000 : ℝ)) (X := (25007009640900649179/25000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024063548752003801/50000000000000000000 : ℝ) ≤ (625073815319509/625000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50024063548752003801/50000000000000000000 : ℝ)^256 ≤ (625073815319509/625000000000000 : ℝ)^1043 := by
      have hnat : (50024063548752003801 : ℕ)^256*625000000000000^1043 ≤ 625073815319509^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024063548752003801 50000000000000000000 625073815319509 625000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073815319509/625000000000000 : ℝ)) (X := (50024063548752003801/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508526953925677311/12500000000000000000 : ℝ) ≤ (1000167396816203/1000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (12508526953925677311/12500000000000000000 : ℝ)^256 ≤ (1000167396816203/1000000000000000 : ℝ)^1043 := by
      have hnat : (12508526953925677311 : ℕ)^256*1000000000000000^1043 ≤ 1000167396816203^1043*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508526953925677311 12500000000000000000 1000167396816203 1000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000167396816203/1000000000000000 : ℝ)) (X := (12508526953925677311/12500000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7009640900649179/50000000000000000000 : ℝ) ≤ ((13810365822473801047/13815000000000000000 : ℝ)+2*(246461524943/138150000000000 : ℝ)*(1133/10000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (13810365822473801047/13815000000000000000 : ℝ)+2*(246461524943/138150000000000 : ℝ)*(1133/10000 : ℝ)=(5000344061031129/5000000000000000 : ℝ) by norm_num, show 1+2*(7009640900649179/50000000000000000000 : ℝ)=(25007009640900649179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8526953925677311/25000000000000000000 : ℝ)+(7009640900649179/50000000000000000000 : ℝ) ≤ ((13810365822473801047/13815000000000000000 : ℝ)+(246461524943/138150000000000 : ℝ)*((14093/100000 : ℝ)+(1133/10000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (13810365822473801047/13815000000000000000 : ℝ)+(246461524943/138150000000000 : ℝ)*((14093/100000 : ℝ)+(1133/10000 : ℝ))=(625073815319509/625000000000000 : ℝ) by norm_num, show 1+(8526953925677311/25000000000000000000 : ℝ)+(7009640900649179/50000000000000000000 : ℝ)=(50024063548752003801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8526953925677311/25000000000000000000 : ℝ) ≤ ((13810365822473801047/13815000000000000000 : ℝ)+2*(246461524943/138150000000000 : ℝ)*(14093/100000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (13810365822473801047/13815000000000000000 : ℝ)+2*(246461524943/138150000000000 : ℝ)*(14093/100000 : ℝ)=(1000167396816203/1000000000000000 : ℝ) by norm_num, show 1+2*(8526953925677311/25000000000000000000 : ℝ)=(12508526953925677311/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13810365822473801047/13815000000000000000 : ℝ)*(X 1 0+X 2 0)+(246461524943/138150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13810365822473801047/13815000000000000000 : ℝ)) (alpha := (246461524943/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13810365822473801047/13815000000000000000 : ℝ)*(X 0 1+X 2 1)+(246461524943/138150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13810365822473801047/13815000000000000000 : ℝ)) (alpha := (246461524943/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13810365822473801047/13815000000000000000 : ℝ)*(X 0 2+X 1 2)+(246461524943/138150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13810365822473801047/13815000000000000000 : ℝ)) (alpha := (246461524943/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43241667/200000000 : ℝ)*X 0 0+(2696590399/5000000000 : ℝ)*X 0 1+(2632795767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344803069/10000000000 : ℝ)*X 1 0+(-278350147/1250000000 : ℝ)*X 1 1+(5265591591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344803337/10000000000 : ℝ)*X 2 0+(42124731/80000000 : ℝ)*X 2 1+(-445360221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181625191/5000000000 : ℝ)*X 0 0+(4237922617/10000000000 : ℝ)*X 0 1+(224612831/500000000 : ℝ)*X 0 2+(2181625191/5000000000 : ℝ)*X 1 0+(4237922617/10000000000 : ℝ)*X 1 1+(224612831/500000000 : ℝ)*X 1 2+(2181625191/5000000000 : ℝ)*X 2 0+(4237922617/10000000000 : ℝ)*X 2 1+(224612831/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-135130531/625000000 : ℝ)*X 0 0+(5265914087/10000000000 : ℝ)*X 0 1+(5392856919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664056771/1250000000 : ℝ)*X 1 0+(-1049767371/5000000000 : ℝ)*X 1 1+(5392857607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062490843/2000000000 : ℝ)*X 2 0+(33705357/62500000 : ℝ)*X 2 1+(-2099535341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363260427/10000000000 : ℝ)*X 0 0+(1122903567/2500000000 : ℝ)*X 0 1+(423856709/1000000000 : ℝ)*X 0 2+(4363260427/10000000000 : ℝ)*X 1 0+(1122903567/2500000000 : ℝ)*X 1 1+(423856709/1000000000 : ℝ)*X 1 2+(4363260427/10000000000 : ℝ)*X 2 0+(1122903567/2500000000 : ℝ)*X 2 1+(423856709/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206698118225448335713064037/19187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812953121/100000000000000 : ℝ)*(base19) + (165720183/10000000000000 : ℝ)*(base23) + (146648623/50000000000000 : ℝ)*(lower2) + (70165501/20000000000000 : ℝ)*(upper3) + (131010387/100000000000000 : ℝ)*(upper5) + (2942405708146987/50000000000000 : ℝ)*(major0) + (2942405708146987/50000000000000 : ℝ)*(major1) + (2942405708146987/50000000000000 : ℝ)*(major2) + (979711423419741/12500000000000 : ℝ)*(sp0) + (979716620247369/12500000000000 : ℝ)*(sp1) + (1959433279432561/25000000000000 : ℝ)*(sp2) + (239981558114/6103515625 : ℝ)*(sp3) + (21693787073/50000000000000 : ℝ)*(sp4) + (29850431407/100000000000000 : ℝ)*(sp7) + (245742981160699/6250000000000 : ℝ)*(f.failure) + (7837734774932073/100000000000000 : ℝ)*(f.sum) + (107737672987889/13815000000000000000000000000 : ℝ)*base65 + (967047647099698463/230250000000000000000000000000000 : ℝ)*base67 + (3464288408749198463/230250000000000000000000000000000 : ℝ)*base69 + (147671064550948463/230250000000000000000000000000000 : ℝ)*base71 + (9160591288303/1726875000000000000000000000 : ℝ)*base73 + (3421923581642698463/230250000000000000000000000000000 : ℝ)*base75 + (370087835215948463/230250000000000000000000000000000 : ℝ)*base77 + (1096449227383801537/230250000000000000000000000000000 : ℝ)*base80 + (58197828048007/6907500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1844129/312500000000000000000 : ℝ)*base90 + (1844129/312500000000000000000 : ℝ)*base92 + (1844129/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61001601627568437101/15350000000000000000000000 : ℝ) := by norm_num
    linear_combination (31315619/2000000000000 : ℝ)*(base19) + (936808093/50000000000000 : ℝ)*(base23) + (458695303/100000000000000 : ℝ)*(upper3) + (161239119/100000000000000 : ℝ)*(lower4) + (1182938732332751/20000000000000 : ℝ)*(major0) + (1182938732332751/20000000000000 : ℝ)*(major1) + (1182938732332751/20000000000000 : ℝ)*(major2) + (63226353393/100000000000000 : ℝ)*(sp1) + (10498142437/20000000000000 : ℝ)*(sp2) + (3387337237/50000000000000 : ℝ)*(sp3) + (3938766959554691/50000000000000 : ℝ)*(sp4) + (7877469126975039/100000000000000 : ℝ)*(sp5) + (7877479554781011/100000000000000 : ℝ)*(sp6) + (1975923248537727/50000000000000 : ℝ)*(sp7) + (493981658968741/12500000000000 : ℝ)*(f.failure) + (3938766959554691/50000000000000 : ℝ)*(f.sum) + (917908116749/172687500000000000000000000 : ℝ)*base65 + (104243711192569901/92100000000000000000000000000000 : ℝ)*base68 + (326754776836030099/92100000000000000000000000000000 : ℝ)*base69 + (656137275232330099/92100000000000000000000000000000 : ℝ)*base71 + (55406803537/1381500000000000000000000000 : ℝ)*base73 + (629867308472230099/92100000000000000000000000000000 : ℝ)*base75 + (1133457552243769901/92100000000000000000000000000000 : ℝ)*base78 + (195228238450669901/92100000000000000000000000000000 : ℝ)*base80 + (1889083441027/1381500000000000000000000000 : ℝ)*base81 + (7166111/625000000000000000000 : ℝ)*base90 + (7166111/625000000000000000000 : ℝ)*base92 + (7166111/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1152_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s7_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081055927/5000000000 : ℝ)*x 0 + (674109529/1250000000 : ℝ)*x 1 + (5265877137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081055927/5000000000 : ℝ)^8345 ≤ (13138862327033/100000000000000 : ℝ)^6297 := by
    have hnat : (1081055927 : ℕ)^8345*100000000000000^6297 ≤ 13138862327033^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081055927 5000000000 13138862327033 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674109529/1250000000 : ℝ)^8345 ≤ (689317506827/1562500000000 : ℝ)^6297 := by
    have hnat : (674109529 : ℕ)^8345*1562500000000^6297 ≤ 689317506827^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674109529 1250000000 689317506827 1562500000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265877137/10000000000 : ℝ)^8345 ≤ (21372408608603/50000000000000 : ℝ)^6297 := by
    have hnat : (5265877137 : ℕ)^8345*50000000000000^6297 ≤ 21372408608603^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265877137 10000000000 21372408608603 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081055927/5000000000 : ℝ), (674109529/1250000000 : ℝ), (5265877137/10000000000 : ℝ)] ![(13138862327033/100000000000000 : ℝ), (689317506827/1562500000000 : ℝ), (21372408608603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081055927/5000000000 : ℝ)|^8345 ≤ (13138862327033/100000000000000 : ℝ)^6297
        have hw : |(-1081055927/5000000000 : ℝ)|=(1081055927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674109529/1250000000 : ℝ)|^8345 ≤ (689317506827/1562500000000 : ℝ)^6297
        have hw : |(674109529/1250000000 : ℝ)|=(674109529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265877137/10000000000 : ℝ)|^8345 ≤ (21372408608603/50000000000000 : ℝ)^6297
        have hw : |(5265877137/10000000000 : ℝ)|=(5265877137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344726071/10000000000 : ℝ)*x 0 + (-222652559/1000000000 : ℝ)*x 1 + (263293863/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344726071/10000000000 : ℝ)^8345 ≤ (4359508140751/10000000000000 : ℝ)^6297 := by
    have hnat : (5344726071 : ℕ)^8345*10000000000000^6297 ≤ 4359508140751^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344726071 10000000000 4359508140751 10000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222652559/1000000000 : ℝ)^8345 ≤ (13660100035499/100000000000000 : ℝ)^6297 := by
    have hnat : (222652559 : ℕ)^8345*100000000000000^6297 ≤ 13660100035499^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222652559 1000000000 13660100035499 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263293863/500000000 : ℝ)^8345 ≤ (1068620463509/2500000000000 : ℝ)^6297 := by
    have hnat : (263293863 : ℕ)^8345*2500000000000^6297 ≤ 1068620463509^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263293863 500000000 1068620463509 2500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344726071/10000000000 : ℝ), (-222652559/1000000000 : ℝ), (263293863/500000000 : ℝ)] ![(4359508140751/10000000000000 : ℝ), (13660100035499/100000000000000 : ℝ), (1068620463509/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344726071/10000000000 : ℝ)|^8345 ≤ (4359508140751/10000000000000 : ℝ)^6297
        have hw : |(5344726071/10000000000 : ℝ)|=(5344726071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222652559/1000000000 : ℝ)|^8345 ≤ (13660100035499/100000000000000 : ℝ)^6297
        have hw : |(-222652559/1000000000 : ℝ)|=(222652559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263293863/500000000 : ℝ)|^8345 ≤ (1068620463509/2500000000000 : ℝ)^6297
        have hw : |(263293863/500000000 : ℝ)|=(263293863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267236307/500000000 : ℝ)*x 0 + (2632938599/5000000000 : ℝ)*x 1 + (-2226525581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267236307/500000000 : ℝ)^8345 ≤ (10898770538341/25000000000000 : ℝ)^6297 := by
    have hnat : (267236307 : ℕ)^8345*25000000000000^6297 ≤ 10898770538341^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267236307 500000000 10898770538341 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632938599/5000000000 : ℝ)^8345 ≤ (8548963574681/20000000000000 : ℝ)^6297 := by
    have hnat : (2632938599 : ℕ)^8345*20000000000000^6297 ≤ 8548963574681^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632938599 5000000000 8548963574681 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226525581/10000000000 : ℝ)^8345 ≤ (3415024990581/25000000000000 : ℝ)^6297 := by
    have hnat : (2226525581 : ℕ)^8345*25000000000000^6297 ≤ 3415024990581^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226525581 10000000000 3415024990581 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267236307/500000000 : ℝ), (2632938599/5000000000 : ℝ), (-2226525581/10000000000 : ℝ)] ![(10898770538341/25000000000000 : ℝ), (8548963574681/20000000000000 : ℝ), (3415024990581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267236307/500000000 : ℝ)|^8345 ≤ (10898770538341/25000000000000 : ℝ)^6297
        have hw : |(267236307/500000000 : ℝ)|=(267236307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632938599/5000000000 : ℝ)|^8345 ≤ (8548963574681/20000000000000 : ℝ)^6297
        have hw : |(2632938599/5000000000 : ℝ)|=(2632938599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226525581/10000000000 : ℝ)|^8345 ≤ (3415024990581/25000000000000 : ℝ)^6297
        have hw : |(-2226525581/10000000000 : ℝ)|=(2226525581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872653039/2000000000 : ℝ)*x 0 + (2119254651/5000000000 : ℝ)*x 1 + (1122916563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872653039/2000000000 : ℝ)^8345 ≤ (4164626190387/12500000000000 : ℝ)^6297 := by
    have hnat : (872653039 : ℕ)^8345*12500000000000^6297 ≤ 4164626190387^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872653039 2000000000 4164626190387 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119254651/5000000000 : ℝ)^8345 ≤ (32060485173021/100000000000000 : ℝ)^6297 := by
    have hnat : (2119254651 : ℕ)^8345*100000000000000^6297 ≤ 32060485173021^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119254651 5000000000 32060485173021 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122916563/2500000000 : ℝ)^8345 ≤ (6924501056103/20000000000000 : ℝ)^6297 := by
    have hnat : (1122916563 : ℕ)^8345*20000000000000^6297 ≤ 6924501056103^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122916563 2500000000 6924501056103 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872653039/2000000000 : ℝ), (2119254651/5000000000 : ℝ), (1122916563/2500000000 : ℝ)] ![(4164626190387/12500000000000 : ℝ), (32060485173021/100000000000000 : ℝ), (6924501056103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872653039/2000000000 : ℝ)|^8345 ≤ (4164626190387/12500000000000 : ℝ)^6297
        have hw : |(872653039/2000000000 : ℝ)|=(872653039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119254651/5000000000 : ℝ)|^8345 ≤ (32060485173021/100000000000000 : ℝ)^6297
        have hw : |(2119254651/5000000000 : ℝ)|=(2119254651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122916563/2500000000 : ℝ)|^8345 ≤ (6924501056103/20000000000000 : ℝ)^6297
        have hw : |(1122916563/2500000000 : ℝ)|=(1122916563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162116523/10000000000 : ℝ)*x 0 + (1053239303/2000000000 : ℝ)*x 1 + (2696277923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162116523/10000000000 : ℝ)^8345 ≤ (13138899927763/100000000000000 : ℝ)^6297 := by
    have hnat : (2162116523 : ℕ)^8345*100000000000000^6297 ≤ 13138899927763^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162116523 10000000000 13138899927763 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053239303/2000000000 : ℝ)^8345 ≤ (2137412645637/5000000000000 : ℝ)^6297 := by
    have hnat : (1053239303 : ℕ)^8345*5000000000000^6297 ≤ 2137412645637^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053239303 2000000000 2137412645637 5000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696277923/5000000000 : ℝ)^8345 ≤ (22056423574401/50000000000000 : ℝ)^6297 := by
    have hnat : (2696277923 : ℕ)^8345*50000000000000^6297 ≤ 22056423574401^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696277923 5000000000 22056423574401 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162116523/10000000000 : ℝ), (1053239303/2000000000 : ℝ), (2696277923/5000000000 : ℝ)] ![(13138899927763/100000000000000 : ℝ), (2137412645637/5000000000000 : ℝ), (22056423574401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162116523/10000000000 : ℝ)|^8345 ≤ (13138899927763/100000000000000 : ℝ)^6297
        have hw : |(-2162116523/10000000000 : ℝ)|=(2162116523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053239303/2000000000 : ℝ)|^8345 ≤ (2137412645637/5000000000000 : ℝ)^6297
        have hw : |(1053239303/2000000000 : ℝ)|=(1053239303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696277923/5000000000 : ℝ)|^8345 ≤ (22056423574401/50000000000000 : ℝ)^6297
        have hw : |(2696277923/5000000000 : ℝ)|=(2696277923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312526577/10000000000 : ℝ)*x 0 + (-2099847087/10000000000 : ℝ)*x 1 + (2696277861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312526577/10000000000 : ℝ)^8345 ≤ (43247363166583/100000000000000 : ℝ)^6297 := by
    have hnat : (5312526577 : ℕ)^8345*100000000000000^6297 ≤ 43247363166583^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312526577 10000000000 43247363166583 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099847087/10000000000 : ℝ)^8345 ≤ (12639791006899/100000000000000 : ℝ)^6297 := by
    have hnat : (2099847087 : ℕ)^8345*100000000000000^6297 ≤ 12639791006899^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099847087 10000000000 12639791006899 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696277861/5000000000 : ℝ)^8345 ≤ (22056422902269/50000000000000 : ℝ)^6297 := by
    have hnat : (2696277861 : ℕ)^8345*50000000000000^6297 ≤ 22056422902269^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696277861 5000000000 22056422902269 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312526577/10000000000 : ℝ), (-2099847087/10000000000 : ℝ), (2696277861/5000000000 : ℝ)] ![(43247363166583/100000000000000 : ℝ), (12639791006899/100000000000000 : ℝ), (22056422902269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312526577/10000000000 : ℝ)|^8345 ≤ (43247363166583/100000000000000 : ℝ)^6297
        have hw : |(5312526577/10000000000 : ℝ)|=(5312526577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099847087/10000000000 : ℝ)|^8345 ≤ (12639791006899/100000000000000 : ℝ)^6297
        have hw : |(-2099847087/10000000000 : ℝ)|=(2099847087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696277861/5000000000 : ℝ)|^8345 ≤ (22056422902269/50000000000000 : ℝ)^6297
        have hw : |(2696277861/5000000000 : ℝ)|=(2696277861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265626321/500000000 : ℝ)*x 0 + (1348138961/2500000000 : ℝ)*x 1 + (-419969427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265626321/500000000 : ℝ)^8345 ≤ (43247361472827/100000000000000 : ℝ)^6297 := by
    have hnat : (265626321 : ℕ)^8345*100000000000000^6297 ≤ 43247361472827^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265626321 500000000 43247361472827 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348138961/2500000000 : ℝ)^8345 ≤ (44112847127121/100000000000000 : ℝ)^6297 := by
    have hnat : (1348138961 : ℕ)^8345*100000000000000^6297 ≤ 44112847127121^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348138961 2500000000 44112847127121 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419969427/2000000000 : ℝ)^8345 ≤ (63198956949/500000000000 : ℝ)^6297 := by
    have hnat : (419969427 : ℕ)^8345*500000000000^6297 ≤ 63198956949^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419969427 2000000000 63198956949 500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265626321/500000000 : ℝ), (1348138961/2500000000 : ℝ), (-419969427/2000000000 : ℝ)] ![(43247361472827/100000000000000 : ℝ), (44112847127121/100000000000000 : ℝ), (63198956949/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265626321/500000000 : ℝ)|^8345 ≤ (43247361472827/100000000000000 : ℝ)^6297
        have hw : |(265626321/500000000 : ℝ)|=(265626321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348138961/2500000000 : ℝ)|^8345 ≤ (44112847127121/100000000000000 : ℝ)^6297
        have hw : |(1348138961/2500000000 : ℝ)|=(1348138961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419969427/2000000000 : ℝ)|^8345 ≤ (63198956949/500000000000 : ℝ)^6297
        have hw : |(-419969427/2000000000 : ℝ)|=(419969427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s7_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090818761/2500000000 : ℝ)*x 0 + (4491029699/10000000000 : ℝ)*x 1 + (2119574003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090818761/2500000000 : ℝ)^8345 ≤ (16658554593667/50000000000000 : ℝ)^6297 := by
    have hnat : (1090818761 : ℕ)^8345*50000000000000^6297 ≤ 16658554593667^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090818761 2500000000 16658554593667 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491029699/10000000000 : ℝ)^8345 ≤ (8654000740577/25000000000000 : ℝ)^6297 := by
    have hnat : (4491029699 : ℕ)^8345*25000000000000^6297 ≤ 8654000740577^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491029699 10000000000 8654000740577 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119574003/5000000000 : ℝ)^8345 ≤ (32066887824693/100000000000000 : ℝ)^6297 := by
    have hnat : (2119574003 : ℕ)^8345*100000000000000^6297 ≤ 32066887824693^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119574003 5000000000 32066887824693 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090818761/2500000000 : ℝ), (4491029699/10000000000 : ℝ), (2119574003/5000000000 : ℝ)] ![(16658554593667/50000000000000 : ℝ), (8654000740577/25000000000000 : ℝ), (32066887824693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090818761/2500000000 : ℝ)|^8345 ≤ (16658554593667/50000000000000 : ℝ)^6297
        have hw : |(1090818761/2500000000 : ℝ)|=(1090818761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491029699/10000000000 : ℝ)|^8345 ≤ (8654000740577/25000000000000 : ℝ)^6297
        have hw : |(4491029699/10000000000 : ℝ)|=(4491029699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119574003/5000000000 : ℝ)|^8345 ≤ (32066887824693/100000000000000 : ℝ)^6297
        have hw : |(2119574003/5000000000 : ℝ)|=(2119574003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11359/100000 : ℝ) ^ (1043/256 : ℝ) ≤ (14166054920634681/100000000000000000000 : ℝ) := by
    have hpowers : (11359/100000 : ℝ)^1043 ≤ (14166054920634681/100000000000000000000 : ℝ)^256 := by
      have hnat : (11359 : ℕ)^1043*100000000000000000000^256 ≤ 14166054920634681^256*100000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359 100000 14166054920634681 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11359/100000 : ℝ)) (X := (14166054920634681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (1043/256 : ℝ) ≤ (33803175066166383/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^1043 ≤ (33803175066166383/100000000000000000000 : ℝ)^256 := by
      have hnat : (7031 : ℕ)^1043*100000000000000000000^256 ≤ 33803175066166383^256*50000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 33803175066166383 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (33803175066166383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014166054920634681/50000000000000000000 : ℝ) ≤ (1000069532550033/1000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50014166054920634681/50000000000000000000 : ℝ)^256 ≤ (1000069532550033/1000000000000000 : ℝ)^1043 := by
      have hnat : (50014166054920634681 : ℕ)^256*1000000000000000^1043 ≤ 1000069532550033^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014166054920634681 50000000000000000000 1000069532550033 1000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000069532550033/1000000000000000 : ℝ)) (X := (50014166054920634681/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505996153748350133/12500000000000000000 : ℝ) ≤ (2500294292930997/2500000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (12505996153748350133/12500000000000000000 : ℝ)^256 ≤ (2500294292930997/2500000000000000 : ℝ)^1043 := by
      have hnat : (12505996153748350133 : ℕ)^256*2500000000000000^1043 ≤ 2500294292930997^1043*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505996153748350133 12500000000000000000 2500294292930997 2500000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500294292930997/2500000000000000 : ℝ)) (X := (12505996153748350133/12500000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033803175066166383/50000000000000000000 : ℝ) ≤ (5000829508973823/5000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50033803175066166383/50000000000000000000 : ℝ)^256 ≤ (5000829508973823/5000000000000000 : ℝ)^1043 := by
      have hnat : (50033803175066166383 : ℕ)^256*5000000000000000^1043 ≤ 5000829508973823^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033803175066166383 50000000000000000000 5000829508973823 5000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000829508973823/5000000000000000 : ℝ)) (X := (50033803175066166383/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14166054920634681/100000000000000000000 : ℝ) ≤ ((4503488813719721591/4505000000000000000 : ℝ)+2*(80307703943/45050000000000 : ℝ)*(11359/100000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (4503488813719721591/4505000000000000000 : ℝ)+2*(80307703943/45050000000000 : ℝ)*(11359/100000 : ℝ)=(1000069532550033/1000000000000000 : ℝ) by norm_num, show 1+2*(14166054920634681/100000000000000000000 : ℝ)=(50014166054920634681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33803175066166383/100000000000000000000 : ℝ)+(14166054920634681/100000000000000000000 : ℝ) ≤ ((4503488813719721591/4505000000000000000 : ℝ)+(80307703943/45050000000000 : ℝ)*((7031/50000 : ℝ)+(11359/100000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (4503488813719721591/4505000000000000000 : ℝ)+(80307703943/45050000000000 : ℝ)*((7031/50000 : ℝ)+(11359/100000 : ℝ))=(2500294292930997/2500000000000000 : ℝ) by norm_num, show 1+(33803175066166383/100000000000000000000 : ℝ)+(14166054920634681/100000000000000000000 : ℝ)=(12505996153748350133/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33803175066166383/100000000000000000000 : ℝ) ≤ ((4503488813719721591/4505000000000000000 : ℝ)+2*(80307703943/45050000000000 : ℝ)*(7031/50000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (4503488813719721591/4505000000000000000 : ℝ)+2*(80307703943/45050000000000 : ℝ)*(7031/50000 : ℝ)=(5000829508973823/5000000000000000 : ℝ) by norm_num, show 1+2*(33803175066166383/100000000000000000000 : ℝ)=(50033803175066166383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4503488813719721591/4505000000000000000 : ℝ)*(X 1 0+X 2 0)+(80307703943/45050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (4503488813719721591/4505000000000000000 : ℝ)) (alpha := (80307703943/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4503488813719721591/4505000000000000000 : ℝ)*(X 0 1+X 2 1)+(80307703943/45050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (4503488813719721591/4505000000000000000 : ℝ)) (alpha := (80307703943/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4503488813719721591/4505000000000000000 : ℝ)*(X 0 2+X 1 2)+(80307703943/45050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (4503488813719721591/4505000000000000000 : ℝ)) (alpha := (80307703943/45050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081055927/5000000000 : ℝ)*X 0 0+(674109529/1250000000 : ℝ)*X 0 1+(5265877137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344726071/10000000000 : ℝ)*X 1 0+(-222652559/1000000000 : ℝ)*X 1 1+(263293863/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267236307/500000000 : ℝ)*X 2 0+(2632938599/5000000000 : ℝ)*X 2 1+(-2226525581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872653039/2000000000 : ℝ)*X 0 0+(2119254651/5000000000 : ℝ)*X 0 1+(1122916563/2500000000 : ℝ)*X 0 2+(872653039/2000000000 : ℝ)*X 1 0+(2119254651/5000000000 : ℝ)*X 1 1+(1122916563/2500000000 : ℝ)*X 1 2+(872653039/2000000000 : ℝ)*X 2 0+(2119254651/5000000000 : ℝ)*X 2 1+(1122916563/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162116523/10000000000 : ℝ)*X 0 0+(1053239303/2000000000 : ℝ)*X 0 1+(2696277923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312526577/10000000000 : ℝ)*X 1 0+(-2099847087/10000000000 : ℝ)*X 1 1+(2696277861/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265626321/500000000 : ℝ)*X 2 0+(1348138961/2500000000 : ℝ)*X 2 1+(-419969427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090818761/2500000000 : ℝ)*X 0 0+(4491029699/10000000000 : ℝ)*X 0 1+(2119574003/5000000000 : ℝ)*X 0 2+(1090818761/2500000000 : ℝ)*X 1 0+(4491029699/10000000000 : ℝ)*X 1 1+(2119574003/5000000000 : ℝ)*X 1 2+(1090818761/2500000000 : ℝ)*X 2 0+(4491029699/10000000000 : ℝ)*X 2 1+(2119574003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2221132572316999601276552721/225250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1162805983/50000000000000 : ℝ)*(base19) + (2426744227/100000000000000 : ℝ)*(base23) + (69913/25000000000000 : ℝ)*(lower2) + (52853457/20000000000000 : ℝ)*(upper3) + (148827681/50000000000000 : ℝ)*(upper5) + (1478050686119381/25000000000000 : ℝ)*(major0) + (1478050686119381/25000000000000 : ℝ)*(major1) + (236488109779101/4000000000000 : ℝ)*(major2) + (7874142479064021/100000000000000 : ℝ)*(sp0) + (984276731057269/12500000000000 : ℝ)*(sp1) + (7874213747325891/100000000000000 : ℝ)*(sp2) + (790030764973223/20000000000000 : ℝ)*(sp3) + (73695006097/100000000000000 : ℝ)*(sp4) + (17580663671/50000000000000 : ℝ)*(sp7) + (246886811637091/6250000000000 : ℝ)*(f.failure) + (3937108087035059/50000000000000 : ℝ)*(f.sum) + (639856451833/4505000000000000000000000000 : ℝ)*base66 + (652804371771755171/112625000000000000000000000000000 : ℝ)*base67 + (104265430778622309/18020000000000000000000000000000 : ℝ)*base70 + (192430690065505171/112625000000000000000000000000000 : ℝ)*base71 + (1555936038333/4505000000000000000000000000 : ℝ)*base74 + (103404842088242309/18020000000000000000000000000000 : ℝ)*base76 + (33861436886672363/6625000000000000000000000000000 : ℝ)*base77 + (68031504183047363/6625000000000000000000000000000 : ℝ)*base79 + (8927997337041/4505000000000000000000000000 : ℝ)*base82 + (2293961/312500000000000000000 : ℝ)*base90 + (2293961/312500000000000000000 : ℝ)*base92 + (5418961/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (325624131540658204773/33125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1760239239/100000000000000 : ℝ)*(base19) + (48981813/2500000000000 : ℝ)*(base23) + (12846717/6250000000000 : ℝ)*(upper3) + (214851329/100000000000000 : ℝ)*(lower4) + (52415449/20000000000000 : ℝ)*(upper5) + (742752918044777/12500000000000 : ℝ)*(major0) + (742752918044777/12500000000000 : ℝ)*(major1) + (742752918044777/12500000000000 : ℝ)*(major2) + (2503090173/6250000000000 : ℝ)*(sp1) + (22374655211/50000000000000 : ℝ)*(sp2) + (7913932989591869/100000000000000 : ℝ)*(sp4) + (3956945589954931/50000000000000 : ℝ)*(sp5) + (247308946281529/3125000000000 : ℝ)*(sp6) + (1985056685726237/50000000000000 : ℝ)*(sp7) + (1985056685726237/50000000000000 : ℝ)*(f.failure) + (7913932989591869/100000000000000 : ℝ)*(f.sum) + (366268965057/265000000000000000000000000 : ℝ)*base66 + (11904814634424571/3312500000000000000000000000000 : ℝ)*base67 + (14130082051862071/3312500000000000000000000000000 : ℝ)*base69 + (11789179524387929/3312500000000000000000000000000 : ℝ)*base72 + (79669592113/66250000000000000000000000 : ℝ)*base74 + (63403619357487071/3312500000000000000000000000000 : ℝ)*base75 + (19084304694012929/3312500000000000000000000000000 : ℝ)*base78 + (42870672953637929/3312500000000000000000000000000 : ℝ)*base80 + (5965143249/132500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3786327/2500000000000000000000 : ℝ)*base90 + (3786327/2500000000000000000000 : ℝ)*base92 + (3786327/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1152_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s8_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135132249/625000000 : ℝ)*x 0 + (134820419/250000000 : ℝ)*x 1 + (263296699/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135132249/625000000 : ℝ)^8345 ≤ (1642361948381/12500000000000 : ℝ)^6297 := by
    have hnat : (135132249 : ℕ)^8345*12500000000000^6297 ≤ 1642361948381^6297*625000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135132249 625000000 1642361948381 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134820419/250000000 : ℝ)^8345 ≤ (22057837849483/50000000000000 : ℝ)^6297 := by
    have hnat : (134820419 : ℕ)^8345*50000000000000^6297 ≤ 22057837849483^6297*250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134820419 250000000 22057837849483 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263296699/500000000 : ℝ)^8345 ≤ (21372714349227/50000000000000 : ℝ)^6297 := by
    have hnat : (263296699 : ℕ)^8345*50000000000000^6297 ≤ 21372714349227^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263296699 500000000 21372714349227 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135132249/625000000 : ℝ), (134820419/250000000 : ℝ), (263296699/500000000 : ℝ)] ![(1642361948381/12500000000000 : ℝ), (22057837849483/50000000000000 : ℝ), (21372714349227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135132249/625000000 : ℝ)|^8345 ≤ (1642361948381/12500000000000 : ℝ)^6297
        have hw : |(-135132249/625000000 : ℝ)|=(135132249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134820419/250000000 : ℝ)|^8345 ≤ (22057837849483/50000000000000 : ℝ)^6297
        have hw : |(134820419/250000000 : ℝ)|=(134820419/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263296699/500000000 : ℝ)|^8345 ≤ (21372714349227/50000000000000 : ℝ)^6297
        have hw : |(263296699/500000000 : ℝ)|=(263296699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344711249/10000000000 : ℝ)*x 0 + (-69577187/312500000 : ℝ)*x 1 + (5265934181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344711249/10000000000 : ℝ)^8345 ≤ (43594921189511/100000000000000 : ℝ)^6297 := by
    have hnat : (5344711249 : ℕ)^8345*100000000000000^6297 ≤ 43594921189511^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344711249 10000000000 43594921189511 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69577187/312500000 : ℝ)^8345 ≤ (426863997847/3125000000000 : ℝ)^6297 := by
    have hnat : (69577187 : ℕ)^8345*3125000000000^6297 ≤ 426863997847^6297*312500000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69577187 312500000 426863997847 3125000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265934181/10000000000 : ℝ)^8345 ≤ (42745430860689/100000000000000 : ℝ)^6297 := by
    have hnat : (5265934181 : ℕ)^8345*100000000000000^6297 ≤ 42745430860689^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265934181 10000000000 42745430860689 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344711249/10000000000 : ℝ), (-69577187/312500000 : ℝ), (5265934181/10000000000 : ℝ)] ![(43594921189511/100000000000000 : ℝ), (426863997847/3125000000000 : ℝ), (42745430860689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344711249/10000000000 : ℝ)|^8345 ≤ (43594921189511/100000000000000 : ℝ)^6297
        have hw : |(5344711249/10000000000 : ℝ)|=(5344711249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69577187/312500000 : ℝ)|^8345 ≤ (426863997847/3125000000000 : ℝ)^6297
        have hw : |(-69577187/312500000 : ℝ)|=(69577187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265934181/10000000000 : ℝ)|^8345 ≤ (42745430860689/100000000000000 : ℝ)^6297
        have hw : |(5265934181/10000000000 : ℝ)|=(5265934181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672355669/5000000000 : ℝ)*x 0 + (5265934059/10000000000 : ℝ)*x 1 + (-2226470027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672355669/5000000000 : ℝ)^8345 ≤ (21797461075777/50000000000000 : ℝ)^6297 := by
    have hnat : (2672355669 : ℕ)^8345*50000000000000^6297 ≤ 21797461075777^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672355669 5000000000 21797461075777 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265934059/10000000000 : ℝ)^8345 ≤ (166974334173/390625000000 : ℝ)^6297 := by
    have hnat : (5265934059 : ℕ)^8345*390625000000^6297 ≤ 166974334173^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265934059 10000000000 166974334173 390625000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226470027/10000000000 : ℝ)^8345 ≤ (6829824140357/50000000000000 : ℝ)^6297 := by
    have hnat : (2226470027 : ℕ)^8345*50000000000000^6297 ≤ 6829824140357^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226470027 10000000000 6829824140357 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672355669/5000000000 : ℝ), (5265934059/10000000000 : ℝ), (-2226470027/10000000000 : ℝ)] ![(21797461075777/50000000000000 : ℝ), (166974334173/390625000000 : ℝ), (6829824140357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672355669/5000000000 : ℝ)|^8345 ≤ (21797461075777/50000000000000 : ℝ)^6297
        have hw : |(2672355669/5000000000 : ℝ)|=(2672355669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265934059/10000000000 : ℝ)|^8345 ≤ (166974334173/390625000000 : ℝ)^6297
        have hw : |(5265934059/10000000000 : ℝ)|=(5265934059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226470027/10000000000 : ℝ)|^8345 ≤ (6829824140357/50000000000000 : ℝ)^6297
        have hw : |(-2226470027/10000000000 : ℝ)|=(2226470027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218163403/500000000 : ℝ)*x 0 + (4238625077/10000000000 : ℝ)*x 1 + (2245774901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218163403/500000000 : ℝ)^8345 ≤ (16658519257333/50000000000000 : ℝ)^6297 := by
    have hnat : (218163403 : ℕ)^8345*50000000000000^6297 ≤ 16658519257333^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218163403 500000000 16658519257333 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238625077/10000000000 : ℝ)^8345 ≤ (8015411432399/25000000000000 : ℝ)^6297 := by
    have hnat : (4238625077 : ℕ)^8345*25000000000000^6297 ≤ 8015411432399^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238625077 10000000000 8015411432399 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245774901/5000000000 : ℝ)^8345 ≤ (4327664466787/12500000000000 : ℝ)^6297 := by
    have hnat : (2245774901 : ℕ)^8345*12500000000000^6297 ≤ 4327664466787^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245774901 5000000000 4327664466787 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218163403/500000000 : ℝ), (4238625077/10000000000 : ℝ), (2245774901/5000000000 : ℝ)] ![(16658519257333/50000000000000 : ℝ), (8015411432399/25000000000000 : ℝ), (4327664466787/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218163403/500000000 : ℝ)|^8345 ≤ (16658519257333/50000000000000 : ℝ)^6297
        have hw : |(218163403/500000000 : ℝ)|=(218163403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238625077/10000000000 : ℝ)|^8345 ≤ (8015411432399/25000000000000 : ℝ)^6297
        have hw : |(4238625077/10000000000 : ℝ)|=(4238625077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245774901/5000000000 : ℝ)|^8345 ≤ (4327664466787/12500000000000 : ℝ)^6297
        have hw : |(2245774901/5000000000 : ℝ)|=(2245774901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540530231/2500000000 : ℝ)*x 0 + (2633126399/5000000000 : ℝ)*x 1 + (2696248363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540530231/2500000000 : ℝ)^8345 ≤ (13138935370241/100000000000000 : ℝ)^6297 := by
    have hnat : (540530231 : ℕ)^8345*100000000000000^6297 ≤ 13138935370241^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540530231 2500000000 13138935370241 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633126399/5000000000 : ℝ)^8345 ≤ (1335901824431/3125000000000 : ℝ)^6297 := by
    have hnat : (2633126399 : ℕ)^8345*3125000000000^6297 ≤ 1335901824431^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633126399 5000000000 1335901824431 3125000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696248363/5000000000 : ℝ)^8345 ≤ (22056103119631/50000000000000 : ℝ)^6297 := by
    have hnat : (2696248363 : ℕ)^8345*50000000000000^6297 ≤ 22056103119631^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696248363 5000000000 22056103119631 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540530231/2500000000 : ℝ), (2633126399/5000000000 : ℝ), (2696248363/5000000000 : ℝ)] ![(13138935370241/100000000000000 : ℝ), (1335901824431/3125000000000 : ℝ), (22056103119631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540530231/2500000000 : ℝ)|^8345 ≤ (13138935370241/100000000000000 : ℝ)^6297
        have hw : |(-540530231/2500000000 : ℝ)|=(540530231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633126399/5000000000 : ℝ)|^8345 ≤ (1335901824431/3125000000000 : ℝ)^6297
        have hw : |(2633126399/5000000000 : ℝ)|=(2633126399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696248363/5000000000 : ℝ)|^8345 ≤ (22056103119631/50000000000000 : ℝ)^6297
        have hw : |(2696248363/5000000000 : ℝ)|=(2696248363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332033829/625000000 : ℝ)*x 0 + (-2099907421/10000000000 : ℝ)*x 1 + (539249671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332033829/625000000 : ℝ)^8345 ≤ (43247521613741/100000000000000 : ℝ)^6297 := by
    have hnat : (332033829 : ℕ)^8345*100000000000000^6297 ≤ 43247521613741^6297*625000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332033829 625000000 43247521613741 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099907421/10000000000 : ℝ)^8345 ≤ (3160068074829/25000000000000 : ℝ)^6297 := by
    have hnat : (2099907421 : ℕ)^8345*25000000000000^6297 ≤ 3160068074829^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099907421 10000000000 3160068074829 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539249671/1000000000 : ℝ)^8345 ≤ (44112206065809/100000000000000 : ℝ)^6297 := by
    have hnat : (539249671 : ℕ)^8345*100000000000000^6297 ≤ 44112206065809^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539249671 1000000000 44112206065809 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332033829/625000000 : ℝ), (-2099907421/10000000000 : ℝ), (539249671/1000000000 : ℝ)] ![(43247521613741/100000000000000 : ℝ), (3160068074829/25000000000000 : ℝ), (44112206065809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332033829/625000000 : ℝ)|^8345 ≤ (43247521613741/100000000000000 : ℝ)^6297
        have hw : |(332033829/625000000 : ℝ)|=(332033829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099907421/10000000000 : ℝ)|^8345 ≤ (3160068074829/25000000000000 : ℝ)^6297
        have hw : |(-2099907421/10000000000 : ℝ)|=(2099907421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539249671/1000000000 : ℝ)|^8345 ≤ (44112206065809/100000000000000 : ℝ)^6297
        have hw : |(539249671/1000000000 : ℝ)|=(539249671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312541251/10000000000 : ℝ)*x 0 + (2696248359/5000000000 : ℝ)*x 1 + (-2099907429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312541251/10000000000 : ℝ)^8345 ≤ (21623760736747/50000000000000 : ℝ)^6297 := by
    have hnat : (5312541251 : ℕ)^8345*50000000000000^6297 ≤ 21623760736747^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312541251 10000000000 21623760736747 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696248359/5000000000 : ℝ)^8345 ≤ (8822441230507/20000000000000 : ℝ)^6297 := by
    have hnat : (2696248359 : ℕ)^8345*20000000000000^6297 ≤ 8822441230507^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696248359 5000000000 8822441230507 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099907429/10000000000 : ℝ)^8345 ≤ (12640272363133/100000000000000 : ℝ)^6297 := by
    have hnat : (2099907429 : ℕ)^8345*100000000000000^6297 ≤ 12640272363133^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099907429 10000000000 12640272363133 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312541251/10000000000 : ℝ), (2696248359/5000000000 : ℝ), (-2099907429/10000000000 : ℝ)] ![(21623760736747/50000000000000 : ℝ), (8822441230507/20000000000000 : ℝ), (12640272363133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312541251/10000000000 : ℝ)|^8345 ≤ (21623760736747/50000000000000 : ℝ)^6297
        have hw : |(5312541251/10000000000 : ℝ)|=(5312541251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696248359/5000000000 : ℝ)|^8345 ≤ (8822441230507/20000000000000 : ℝ)^6297
        have hw : |(2696248359/5000000000 : ℝ)|=(2696248359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099907429/10000000000 : ℝ)|^8345 ≤ (12640272363133/100000000000000 : ℝ)^6297
        have hw : |(-2099907429/10000000000 : ℝ)|=(2099907429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s8_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436327773/1000000000 : ℝ)*x 0 + (2245457213/5000000000 : ℝ)*x 1 + (4239262753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436327773/1000000000 : ℝ)^8345 ≤ (16658568183791/50000000000000 : ℝ)^6297 := by
    have hnat : (436327773 : ℕ)^8345*50000000000000^6297 ≤ 16658568183791^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436327773 1000000000 16658568183791 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245457213/5000000000 : ℝ)^8345 ≤ (34614825493467/100000000000000 : ℝ)^6297 := by
    have hnat : (2245457213 : ℕ)^8345*100000000000000^6297 ≤ 34614825493467^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245457213 5000000000 34614825493467 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239262753/10000000000 : ℝ)^8345 ≤ (501063095823/1562500000000 : ℝ)^6297 := by
    have hnat : (4239262753 : ℕ)^8345*1562500000000^6297 ≤ 501063095823^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239262753 10000000000 501063095823 1562500000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436327773/1000000000 : ℝ), (2245457213/5000000000 : ℝ), (4239262753/10000000000 : ℝ)] ![(16658568183791/50000000000000 : ℝ), (34614825493467/100000000000000 : ℝ), (501063095823/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436327773/1000000000 : ℝ)|^8345 ≤ (16658568183791/50000000000000 : ℝ)^6297
        have hw : |(436327773/1000000000 : ℝ)|=(436327773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245457213/5000000000 : ℝ)|^8345 ≤ (34614825493467/100000000000000 : ℝ)^6297
        have hw : |(2245457213/5000000000 : ℝ)|=(2245457213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239262753/10000000000 : ℝ)|^8345 ≤ (501063095823/1562500000000 : ℝ)^6297
        have hw : |(4239262753/10000000000 : ℝ)|=(4239262753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (1043/256 : ℝ) ≤ (1774570745114931/12500000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^1043 ≤ (1774570745114931/12500000000000000000 : ℝ)^256 := by
      have hnat : (2273 : ℕ)^1043*12500000000000000000^256 ≤ 1774570745114931^256*20000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 1774570745114931 12500000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (1774570745114931/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (1043/256 : ℝ) ≤ (33744450319732049/100000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^1043 ≤ (33744450319732049/100000000000000000000 : ℝ)^256 := by
      have hnat : (1757 : ℕ)^1043*100000000000000000000^256 ≤ 33744450319732049^256*12500^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 33744450319732049 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (33744450319732049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251774570745114931/6250000000000000000 : ℝ) ≤ (10000696822941389/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (6251774570745114931/6250000000000000000 : ℝ)^256 ≤ (10000696822941389/10000000000000000 : ℝ)^1043 := by
      have hnat : (6251774570745114931 : ℕ)^256*10000000000000000^1043 ≤ 10000696822941389^1043*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251774570745114931 6250000000000000000 10000696822941389 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696822941389/10000000000000000 : ℝ)) (X := (6251774570745114931/6250000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047941016280651497/100000000000000000000 : ℝ) ≤ (10001176479480809/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (100047941016280651497/100000000000000000000 : ℝ)^256 ≤ (10001176479480809/10000000000000000 : ℝ)^1043 := by
      have hnat : (100047941016280651497 : ℕ)^256*10000000000000000^1043 ≤ 10001176479480809^1043*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047941016280651497 100000000000000000000 10001176479480809 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001176479480809/10000000000000000 : ℝ)) (X := (100047941016280651497/100000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033744450319732049/50000000000000000000 : ℝ) ≤ (10001656136020229/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50033744450319732049/50000000000000000000 : ℝ)^256 ≤ (10001656136020229/10000000000000000 : ℝ)^1043 := by
      have hnat : (50033744450319732049 : ℕ)^256*10000000000000000^1043 ≤ 10001656136020229^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033744450319732049 50000000000000000000 10001656136020229 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001656136020229/10000000000000000 : ℝ)) (X := (50033744450319732049/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1774570745114931/12500000000000000000 : ℝ) ≤ ((8966990852464753733/8970000000000000000 : ℝ)+2*(7994275657/4485000000000 : ℝ)*(2273/20000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (8966990852464753733/8970000000000000000 : ℝ)+2*(7994275657/4485000000000 : ℝ)*(2273/20000 : ℝ)=(10000696822941389/10000000000000000 : ℝ) by norm_num, show 1+2*(1774570745114931/12500000000000000000 : ℝ)=(6251774570745114931/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33744450319732049/100000000000000000000 : ℝ)+(1774570745114931/12500000000000000000 : ℝ) ≤ ((8966990852464753733/8970000000000000000 : ℝ)+(7994275657/4485000000000 : ℝ)*((1757/12500 : ℝ)+(2273/20000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (8966990852464753733/8970000000000000000 : ℝ)+(7994275657/4485000000000 : ℝ)*((1757/12500 : ℝ)+(2273/20000 : ℝ))=(10001176479480809/10000000000000000 : ℝ) by norm_num, show 1+(33744450319732049/100000000000000000000 : ℝ)+(1774570745114931/12500000000000000000 : ℝ)=(100047941016280651497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33744450319732049/100000000000000000000 : ℝ) ≤ ((8966990852464753733/8970000000000000000 : ℝ)+2*(7994275657/4485000000000 : ℝ)*(1757/12500 : ℝ))^(1043/256 : ℝ) := by
    rw [show (8966990852464753733/8970000000000000000 : ℝ)+2*(7994275657/4485000000000 : ℝ)*(1757/12500 : ℝ)=(10001656136020229/10000000000000000 : ℝ) by norm_num, show 1+2*(33744450319732049/100000000000000000000 : ℝ)=(50033744450319732049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8966990852464753733/8970000000000000000 : ℝ)*(X 1 0+X 2 0)+(7994275657/4485000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (8966990852464753733/8970000000000000000 : ℝ)) (alpha := (7994275657/4485000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8966990852464753733/8970000000000000000 : ℝ)*(X 0 1+X 2 1)+(7994275657/4485000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (8966990852464753733/8970000000000000000 : ℝ)) (alpha := (7994275657/4485000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8966990852464753733/8970000000000000000 : ℝ)*(X 0 2+X 1 2)+(7994275657/4485000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (8966990852464753733/8970000000000000000 : ℝ)) (alpha := (7994275657/4485000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135132249/625000000 : ℝ)*X 0 0+(134820419/250000000 : ℝ)*X 0 1+(263296699/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344711249/10000000000 : ℝ)*X 1 0+(-69577187/312500000 : ℝ)*X 1 1+(5265934181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672355669/5000000000 : ℝ)*X 2 0+(5265934059/10000000000 : ℝ)*X 2 1+(-2226470027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218163403/500000000 : ℝ)*X 0 0+(4238625077/10000000000 : ℝ)*X 0 1+(2245774901/5000000000 : ℝ)*X 0 2+(218163403/500000000 : ℝ)*X 1 0+(4238625077/10000000000 : ℝ)*X 1 1+(2245774901/5000000000 : ℝ)*X 1 2+(218163403/500000000 : ℝ)*X 2 0+(4238625077/10000000000 : ℝ)*X 2 1+(2245774901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-540530231/2500000000 : ℝ)*X 0 0+(2633126399/5000000000 : ℝ)*X 0 1+(2696248363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332033829/625000000 : ℝ)*X 1 0+(-2099907421/10000000000 : ℝ)*X 1 1+(539249671/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312541251/10000000000 : ℝ)*X 2 0+(2696248359/5000000000 : ℝ)*X 2 1+(-2099907429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436327773/1000000000 : ℝ)*X 0 0+(2245457213/5000000000 : ℝ)*X 0 1+(4239262753/10000000000 : ℝ)*X 0 2+(436327773/1000000000 : ℝ)*X 1 0+(2245457213/5000000000 : ℝ)*X 1 1+(4239262753/10000000000 : ℝ)*X 1 2+(436327773/1000000000 : ℝ)*X 2 0+(2245457213/5000000000 : ℝ)*X 2 1+(4239262753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (287851875299457771974651983/74750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (609335241/100000000000000 : ℝ)*(base19) + (12691753/2000000000000 : ℝ)*(base23) + (7080907/12500000000000 : ℝ)*(lower2) + (134733593/100000000000000 : ℝ)*(upper3) + (11365879/100000000000000 : ℝ)*(upper5) + (2958776593605251/50000000000000 : ℝ)*(major0) + (2958776593605251/50000000000000 : ℝ)*(major1) + (5917553187210503/100000000000000 : ℝ)*(major2) + (7881317742911689/100000000000000 : ℝ)*(sp0) + (7881341796813543/100000000000000 : ℝ)*(sp1) + (3940670885780567/50000000000000 : ℝ)*(sp2) + (988438193831811/25000000000000 : ℝ)*(sp3) + (4932647419/20000000000000 : ℝ)*(sp4) + (691536433/6250000000000 : ℝ)*(sp7) + (988440959977543/25000000000000 : ℝ)*(f.failure) + (492583900384299/6250000000000 : ℝ)*(f.sum) + (31158933089/11500000000000000000000000 : ℝ)*base65 + (2463389971016449339/149500000000000000000000000000000 : ℝ)*base68 + (2505121525980019233/299000000000000000000000000000000 : ℝ)*base69 + (596935020194050661/149500000000000000000000000000000 : ℝ)*base71 + (1963556431/11500000000000000000000000 : ℝ)*base74 + (2988665631826980767/299000000000000000000000000000000 : ℝ)*base76 + (8632387215197348017/448500000000000000000000000000000 : ℝ)*base78 + (5698803723722348017/448500000000000000000000000000000 : ℝ)*base80 + (103648099109/448500000000000000000000000 : ℝ)*base81 + (8227947/1250000000000000000000 : ℝ)*base89 + (8227947/1250000000000000000000 : ℝ)*base91 + (4272053/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (200171437311800598066060189/74750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (517602987/100000000000000 : ℝ)*(base19) + (535119331/100000000000000 : ℝ)*(base23) + (149452981/100000000000000 : ℝ)*(lower1) + (2210669/10000000000000 : ℝ)*(upper2) + (66509483/100000000000000 : ℝ)*(upper3) + (99484977/100000000000000 : ℝ)*(upper5) + (2973725426489033/50000000000000 : ℝ)*(major0) + (2973725426489033/50000000000000 : ℝ)*(major1) + (2973725426489033/50000000000000 : ℝ)*(major2) + (19455637/2500000000000 : ℝ)*(sp1) + (3960580950297163/50000000000000 : ℝ)*(sp4) + (7921160604765859/100000000000000 : ℝ)*(sp5) + (1584232273094999/20000000000000 : ℝ)*(sp6) + (124179366128099/3125000000000 : ℝ)*(sp7) + (124179366128099/3125000000000 : ℝ)*(f.failure) + (3960580950297163/50000000000000 : ℝ)*(f.sum) + (438212147669/56062500000000000000000000 : ℝ)*base66 + (6799442989093689811/448500000000000000000000000000000 : ℝ)*base68 + (19354724868802310189/448500000000000000000000000000000 : ℝ)*base69 + (2724074732263689811/448500000000000000000000000000000 : ℝ)*base72 + (237637091753/35880000000000000000000000 : ℝ)*base74 + (3171537054856689811/448500000000000000000000000000000 : ℝ)*base76 + (2695455251640189811/448500000000000000000000000000000 : ℝ)*base78 + (1323725206399310189/448500000000000000000000000000000 : ℝ)*base79 + (4102287165659/179400000000000000000000000 : ℝ)*base81 + (1395471/156250000000000000000 : ℝ)*base89 + (1395471/156250000000000000000 : ℝ)*base91 + (1395471/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1152_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1152_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1152_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1152_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1152_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
