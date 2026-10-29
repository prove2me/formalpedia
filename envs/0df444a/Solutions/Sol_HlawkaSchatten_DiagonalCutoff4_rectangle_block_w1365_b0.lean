-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:26.049282+00:00
-- url     : https://prove2.me/submissions/bb59d05e-74dc-47ae-94db-2a6780fa8d8f

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
theorem support_rectangle_w1365_s0_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179562707/1000000000 : ℝ)*x 0 + (1496760557/2500000000 : ℝ)*x 1 + (2408183423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179562707/1000000000 : ℝ)^4325 ≤ (2108129351127/20000000000000 : ℝ)^3301 := by
    have hnat : (179562707 : ℕ)^4325*20000000000000^3301 ≤ 2108129351127^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179562707 1000000000 2108129351127 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1496760557/2500000000 : ℝ)^4325 ≤ (2553122050659/5000000000000 : ℝ)^3301 := by
    have hnat : (1496760557 : ℕ)^4325*5000000000000^3301 ≤ 2553122050659^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496760557 2500000000 2553122050659 5000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2408183423/5000000000 : ℝ)^4325 ≤ (2399807013581/6250000000000 : ℝ)^3301 := by
    have hnat : (2408183423 : ℕ)^4325*6250000000000^3301 ≤ 2399807013581^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408183423 5000000000 2399807013581 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179562707/1000000000 : ℝ), (1496760557/2500000000 : ℝ), (2408183423/5000000000 : ℝ)] ![(2108129351127/20000000000000 : ℝ), (2553122050659/5000000000000 : ℝ), (2399807013581/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179562707/1000000000 : ℝ)|^4325 ≤ (2108129351127/20000000000000 : ℝ)^3301
        have hw : |(-179562707/1000000000 : ℝ)|=(179562707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1496760557/2500000000 : ℝ)|^4325 ≤ (2553122050659/5000000000000 : ℝ)^3301
        have hw : |(1496760557/2500000000 : ℝ)|=(1496760557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2408183423/5000000000 : ℝ)|^4325 ≤ (2399807013581/6250000000000 : ℝ)^3301
        have hw : |(2408183423/5000000000 : ℝ)|=(2408183423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099847739/2000000000 : ℝ)*x 0 + (-2459929043/10000000000 : ℝ)*x 1 + (4816367381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099847739/2000000000 : ℝ)^4325 ≤ (11420420432083/25000000000000 : ℝ)^3301 := by
    have hnat : (1099847739 : ℕ)^4325*25000000000000^3301 ≤ 11420420432083^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099847739 2000000000 11420420432083 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459929043/10000000000 : ℝ)^4325 ≤ (7960700226897/50000000000000 : ℝ)^3301 := by
    have hnat : (2459929043 : ℕ)^4325*50000000000000^3301 ≤ 7960700226897^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459929043 10000000000 7960700226897 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4816367381/10000000000 : ℝ)^4325 ≤ (7679383561097/20000000000000 : ℝ)^3301 := by
    have hnat : (4816367381 : ℕ)^4325*20000000000000^3301 ≤ 7679383561097^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816367381 10000000000 7679383561097 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099847739/2000000000 : ℝ), (-2459929043/10000000000 : ℝ), (4816367381/10000000000 : ℝ)] ![(11420420432083/25000000000000 : ℝ), (7960700226897/50000000000000 : ℝ), (7679383561097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099847739/2000000000 : ℝ)|^4325 ≤ (11420420432083/25000000000000 : ℝ)^3301
        have hw : |(1099847739/2000000000 : ℝ)|=(1099847739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2459929043/10000000000 : ℝ)|^4325 ≤ (7960700226897/50000000000000 : ℝ)^3301
        have hw : |(-2459929043/10000000000 : ℝ)|=(2459929043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4816367381/10000000000 : ℝ)|^4325 ≤ (7679383561097/20000000000000 : ℝ)^3301
        have hw : |(4816367381/10000000000 : ℝ)|=(4816367381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343702411/625000000 : ℝ)*x 0 + (4816366811/10000000000 : ℝ)*x 1 + (-1229964949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343702411/625000000 : ℝ)^4325 ≤ (45681680433161/100000000000000 : ℝ)^3301 := by
    have hnat : (343702411 : ℕ)^4325*100000000000000^3301 ≤ 45681680433161^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343702411 625000000 45681680433161 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4816366811/10000000000 : ℝ)^4325 ≤ (38396911851713/100000000000000 : ℝ)^3301 := by
    have hnat : (4816366811 : ℕ)^4325*100000000000000^3301 ≤ 38396911851713^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816366811 10000000000 38396911851713 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229964949/5000000000 : ℝ)^4325 ≤ (3980351926063/25000000000000 : ℝ)^3301 := by
    have hnat : (1229964949 : ℕ)^4325*25000000000000^3301 ≤ 3980351926063^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229964949 5000000000 3980351926063 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343702411/625000000 : ℝ), (4816366811/10000000000 : ℝ), (-1229964949/5000000000 : ℝ)] ![(45681680433161/100000000000000 : ℝ), (38396911851713/100000000000000 : ℝ), (3980351926063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343702411/625000000 : ℝ)|^4325 ≤ (45681680433161/100000000000000 : ℝ)^3301
        have hw : |(343702411/625000000 : ℝ)|=(343702411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4816366811/10000000000 : ℝ)|^4325 ≤ (38396911851713/100000000000000 : ℝ)^3301
        have hw : |(4816366811/10000000000 : ℝ)|=(4816366811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229964949/5000000000 : ℝ)|^4325 ≤ (3980351926063/25000000000000 : ℝ)^3301
        have hw : |(-1229964949/5000000000 : ℝ)|=(1229964949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4175323987/10000000000 : ℝ)*x 0 + (3105503769/10000000000 : ℝ)*x 1 + (2789401623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175323987/10000000000 : ℝ)^4325 ≤ (15921898630137/50000000000000 : ℝ)^3301 := by
    have hnat : (4175323987 : ℕ)^4325*50000000000000^3301 ≤ 15921898630137^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175323987 10000000000 15921898630137 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105503769/10000000000 : ℝ)^4325 ≤ (4321324070603/20000000000000 : ℝ)^3301 := by
    have hnat : (3105503769 : ℕ)^4325*20000000000000^3301 ≤ 4321324070603^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105503769 10000000000 4321324070603 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2789401623/5000000000 : ℝ)^4325 ≤ (5818697795923/12500000000000 : ℝ)^3301 := by
    have hnat : (2789401623 : ℕ)^4325*12500000000000^3301 ≤ 5818697795923^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789401623 5000000000 5818697795923 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175323987/10000000000 : ℝ), (3105503769/10000000000 : ℝ), (2789401623/5000000000 : ℝ)] ![(15921898630137/50000000000000 : ℝ), (4321324070603/20000000000000 : ℝ), (5818697795923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175323987/10000000000 : ℝ)|^4325 ≤ (15921898630137/50000000000000 : ℝ)^3301
        have hw : |(4175323987/10000000000 : ℝ)|=(4175323987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105503769/10000000000 : ℝ)|^4325 ≤ (4321324070603/20000000000000 : ℝ)^3301
        have hw : |(3105503769/10000000000 : ℝ)|=(3105503769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2789401623/5000000000 : ℝ)|^4325 ≤ (5818697795923/12500000000000 : ℝ)^3301
        have hw : |(2789401623/5000000000 : ℝ)|=(2789401623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-44999111/250000000 : ℝ)*x 0 + (4846454451/10000000000 : ℝ)*x 1 + (372242471/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44999111/250000000 : ℝ)^4325 ≤ (10574018642693/100000000000000 : ℝ)^3301 := by
    have hnat : (44999111 : ℕ)^4325*100000000000000^3301 ≤ 10574018642693^3301*250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44999111 250000000 10574018642693 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846454451/10000000000 : ℝ)^4325 ≤ (38711487752461/100000000000000 : ℝ)^3301 := by
    have hnat : (4846454451 : ℕ)^4325*100000000000000^3301 ≤ 38711487752461^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846454451 10000000000 38711487752461 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372242471/625000000 : ℝ)^4325 ≤ (50714493587717/100000000000000 : ℝ)^3301 := by
    have hnat : (372242471 : ℕ)^4325*100000000000000^3301 ≤ 50714493587717^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372242471 625000000 50714493587717 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44999111/250000000 : ℝ), (4846454451/10000000000 : ℝ), (372242471/625000000 : ℝ)] ![(10574018642693/100000000000000 : ℝ), (38711487752461/100000000000000 : ℝ), (50714493587717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44999111/250000000 : ℝ)|^4325 ≤ (10574018642693/100000000000000 : ℝ)^3301
        have hw : |(-44999111/250000000 : ℝ)|=(44999111/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4846454451/10000000000 : ℝ)|^4325 ≤ (38711487752461/100000000000000 : ℝ)^3301
        have hw : |(4846454451/10000000000 : ℝ)|=(4846454451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(372242471/625000000 : ℝ)|^4325 ≤ (50714493587717/100000000000000 : ℝ)^3301
        have hw : |(372242471/625000000 : ℝ)|=(372242471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2590025779/5000000000 : ℝ)*x 0 + (-52816763/400000000 : ℝ)*x 1 + (595587863/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590025779/5000000000 : ℝ)^4325 ≤ (8447883799719/20000000000000 : ℝ)^3301 := by
    have hnat : (2590025779 : ℕ)^4325*20000000000000^3301 ≤ 8447883799719^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590025779 5000000000 8447883799719 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52816763/400000000 : ℝ)^4325 ≤ (1761524376953/25000000000000 : ℝ)^3301 := by
    have hnat : (52816763 : ℕ)^4325*25000000000000^3301 ≤ 1761524376953^3301*400000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52816763 400000000 1761524376953 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595587863/1000000000 : ℝ)^4325 ≤ (12678620869989/25000000000000 : ℝ)^3301 := by
    have hnat : (595587863 : ℕ)^4325*25000000000000^3301 ≤ 12678620869989^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595587863 1000000000 12678620869989 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590025779/5000000000 : ℝ), (-52816763/400000000 : ℝ), (595587863/1000000000 : ℝ)] ![(8447883799719/20000000000000 : ℝ), (1761524376953/25000000000000 : ℝ), (12678620869989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590025779/5000000000 : ℝ)|^4325 ≤ (8447883799719/20000000000000 : ℝ)^3301
        have hw : |(2590025779/5000000000 : ℝ)|=(2590025779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52816763/400000000 : ℝ)|^4325 ≤ (1761524376953/25000000000000 : ℝ)^3301
        have hw : |(-52816763/400000000 : ℝ)|=(52816763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(595587863/1000000000 : ℝ)|^4325 ≤ (12678620869989/25000000000000 : ℝ)^3301
        have hw : |(595587863/1000000000 : ℝ)|=(595587863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180051123/10000000000 : ℝ)*x 0 + (1488969997/2500000000 : ℝ)*x 1 + (-330104393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180051123/10000000000 : ℝ)^4325 ≤ (10559853587789/25000000000000 : ℝ)^3301 := by
    have hnat : (5180051123 : ℕ)^4325*25000000000000^3301 ≤ 10559853587789^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180051123 10000000000 10559853587789 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1488969997/2500000000 : ℝ)^4325 ≤ (50714498630441/100000000000000 : ℝ)^3301 := by
    have hnat : (1488969997 : ℕ)^4325*100000000000000^3301 ≤ 50714498630441^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488969997 2500000000 50714498630441 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330104393/2500000000 : ℝ)^4325 ≤ (3523043499709/50000000000000 : ℝ)^3301 := by
    have hnat : (330104393 : ℕ)^4325*50000000000000^3301 ≤ 3523043499709^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330104393 2500000000 3523043499709 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180051123/10000000000 : ℝ), (1488969997/2500000000 : ℝ), (-330104393/2500000000 : ℝ)] ![(10559853587789/25000000000000 : ℝ), (50714498630441/100000000000000 : ℝ), (3523043499709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180051123/10000000000 : ℝ)|^4325 ≤ (10559853587789/25000000000000 : ℝ)^3301
        have hw : |(5180051123/10000000000 : ℝ)|=(5180051123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1488969997/2500000000 : ℝ)|^4325 ≤ (50714498630441/100000000000000 : ℝ)^3301
        have hw : |(1488969997/2500000000 : ℝ)|=(1488969997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-330104393/2500000000 : ℝ)|^4325 ≤ (3523043499709/50000000000000 : ℝ)^3301
        have hw : |(-330104393/2500000000 : ℝ)|=(330104393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s0_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184482211/10000000000 : ℝ)*x 0 + (2757619461/5000000000 : ℝ)*x 1 + (198208883/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184482211/10000000000 : ℝ)^4325 ≤ (31935342163549/100000000000000 : ℝ)^3301 := by
    have hnat : (4184482211 : ℕ)^4325*100000000000000^3301 ≤ 31935342163549^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184482211 10000000000 31935342163549 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757619461/5000000000 : ℝ)^4325 ≤ (22927951676391/50000000000000 : ℝ)^3301 := by
    have hnat : (2757619461 : ℕ)^4325*50000000000000^3301 ≤ 22927951676391^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757619461 5000000000 22927951676391 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198208883/625000000 : ℝ)^4325 ≤ (22208754471037/100000000000000 : ℝ)^3301 := by
    have hnat : (198208883 : ℕ)^4325*100000000000000^3301 ≤ 22208754471037^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198208883 625000000 22208754471037 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184482211/10000000000 : ℝ), (2757619461/5000000000 : ℝ), (198208883/625000000 : ℝ)] ![(31935342163549/100000000000000 : ℝ), (22927951676391/50000000000000 : ℝ), (22208754471037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184482211/10000000000 : ℝ)|^4325 ≤ (31935342163549/100000000000000 : ℝ)^3301
        have hw : |(4184482211/10000000000 : ℝ)|=(4184482211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757619461/5000000000 : ℝ)|^4325 ≤ (22927951676391/50000000000000 : ℝ)^3301
        have hw : |(2757619461/5000000000 : ℝ)|=(2757619461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198208883/625000000 : ℝ)|^4325 ≤ (22208754471037/100000000000000 : ℝ)^3301
        have hw : |(198208883/625000000 : ℝ)|=(198208883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (317/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26707/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1081/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1081 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1081*1^256 ≤ 0^256*1^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1081/256 : ℝ) ≤ (2087546389941910903/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1081 ≤ (2087546389941910903/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1081*100000000000000000000^256 ≤ 2087546389941910903^256*5^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2087546389941910903 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2087546389941910903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1081 := by
      have hnat : (1 : ℕ)^256*1^1081 ≤ 1^1081*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102087546389941910903/100000000000000000000 : ℝ) ≤ (10049047761099439/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (102087546389941910903/100000000000000000000 : ℝ)^256 ≤ (10049047761099439/10000000000000000 : ℝ)^1081 := by
      have hnat : (102087546389941910903 : ℕ)^256*10000000000000000^1081 ≤ 10049047761099439^1081*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102087546389941910903 100000000000000000000 10049047761099439 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049047761099439/10000000000000000 : ℝ)) (X := (102087546389941910903/100000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52087546389941910903/50000000000000000000 : ℝ) ≤ (5049047761099439/5000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (52087546389941910903/50000000000000000000 : ℝ)^256 ≤ (5049047761099439/5000000000000000 : ℝ)^1081 := by
      have hnat : (52087546389941910903 : ℕ)^256*5000000000000000^1081 ≤ 5049047761099439^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52087546389941910903 50000000000000000000 5049047761099439 5000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049047761099439/5000000000000000 : ℝ)) (X := (52087546389941910903/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49047761099439/4000000000000000 : ℝ)*(0 : ℝ))^(1081/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(49047761099439/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2087546389941910903/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49047761099439/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (1 : ℝ)+(49047761099439/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049047761099439/10000000000000000 : ℝ) by norm_num, show 1+(2087546389941910903/100000000000000000000 : ℝ)+(0 : ℝ)=(102087546389941910903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2087546389941910903/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49047761099439/4000000000000000 : ℝ)*(2/5 : ℝ))^(1081/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(49047761099439/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049047761099439/5000000000000000 : ℝ) by norm_num, show 1+2*(2087546389941910903/100000000000000000000 : ℝ)=(52087546389941910903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49047761099439/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49047761099439/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49047761099439/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49047761099439/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49047761099439/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49047761099439/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-179562707/1000000000 : ℝ)*X 0 0+(1496760557/2500000000 : ℝ)*X 0 1+(2408183423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099847739/2000000000 : ℝ)*X 1 0+(-2459929043/10000000000 : ℝ)*X 1 1+(4816367381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((343702411/625000000 : ℝ)*X 2 0+(4816366811/10000000000 : ℝ)*X 2 1+(-1229964949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4175323987/10000000000 : ℝ)*X 0 0+(3105503769/10000000000 : ℝ)*X 0 1+(2789401623/5000000000 : ℝ)*X 0 2+(4175323987/10000000000 : ℝ)*X 1 0+(3105503769/10000000000 : ℝ)*X 1 1+(2789401623/5000000000 : ℝ)*X 1 2+(4175323987/10000000000 : ℝ)*X 2 0+(3105503769/10000000000 : ℝ)*X 2 1+(2789401623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44999111/250000000 : ℝ)*X 0 0+(4846454451/10000000000 : ℝ)*X 0 1+(372242471/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2590025779/5000000000 : ℝ)*X 1 0+(-52816763/400000000 : ℝ)*X 1 1+(595587863/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5180051123/10000000000 : ℝ)*X 2 0+(1488969997/2500000000 : ℝ)*X 2 1+(-330104393/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4184482211/10000000000 : ℝ)*X 0 0+(2757619461/5000000000 : ℝ)*X 0 1+(198208883/625000000 : ℝ)*X 0 2+(4184482211/10000000000 : ℝ)*X 1 0+(2757619461/5000000000 : ℝ)*X 1 1+(198208883/625000000 : ℝ)*X 1 2+(4184482211/10000000000 : ℝ)*X 2 0+(2757619461/5000000000 : ℝ)*X 2 1+(198208883/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (400331144922057200054847/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201702803/100000000000000 : ℝ)*(base1) + (372349743/20000000000000 : ℝ)*(base19) + (460815999/25000000000000 : ℝ)*(base23) + (308216357/100000000000000 : ℝ)*(upper3) + (40895759/50000000000000 : ℝ)*(upper5) + (314635826175909/50000000000000 : ℝ)*(major0) + (314635826175909/50000000000000 : ℝ)*(major1) + (314635826175909/50000000000000 : ℝ)*(major2) + (26694194838393/3125000000000 : ℝ)*(sp0) + (170843496833207/20000000000000 : ℝ)*(sp1) + (427108751325377/50000000000000 : ℝ)*(sp2) + (101080116649983/25000000000000 : ℝ)*(sp3) + (5312788977/100000000000000 : ℝ)*(sp4) + (755899679/25000000000000 : ℝ)*(sp7) + (404323691901451/100000000000000 : ℝ)*(f.failure) + (3416877383659/400000000000 : ℝ)*(f.sum) + (98760879215051/100000000000000000000000000000 : ℝ)*base65 + (582096492215051/200000000000000000000000000000 : ℝ)*base67 + (883918277615051/200000000000000000000000000000 : ℝ)*base69 + (961841998215051/200000000000000000000000000000 : ℝ)*base71 + (229782480284949/100000000000000000000000000000 : ℝ)*base74 + (1719590604215051/200000000000000000000000000000 : ℝ)*base75 + (1126729602415051/200000000000000000000000000000 : ℝ)*base77 + (895850184415051/200000000000000000000000000000 : ℝ)*base79 + (142055527584949/100000000000000000000000000000 : ℝ)*base82 + (7481747/2500000000000000000000 : ℝ)*base90 + (7481747/2500000000000000000000 : ℝ)*base92 + (7481747/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1045902344790919348204821/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375606487/25000000000000 : ℝ)*(base19) + (1908593821/100000000000000 : ℝ)*(base23) + (474416429/100000000000000 : ℝ)*(base39) + (884107/781250000000 : ℝ)*(upper3) + (35713311/10000000000000 : ℝ)*(upper5) + (20750082554479/3125000000000 : ℝ)*(major0) + (20750082554479/3125000000000 : ℝ)*(major1) + (332001083663449/50000000000000 : ℝ)*(major2) + (1811170827/50000000000000 : ℝ)*(sp1) + (1962702017/50000000000000 : ℝ)*(sp2) + (225341297151789/25000000000000 : ℝ)*(sp4) + (450680031919777/50000000000000 : ℝ)*(sp5) + (90135982902573/10000000000000 : ℝ)*(sp6) + (426639271828949/100000000000000 : ℝ)*(sp7) + (426639271828949/100000000000000 : ℝ)*(f.failure) + (28167676969487/3125000000000 : ℝ)*(f.sum) + (45522159698393/200000000000000000000000000000 : ℝ)*base66 + (160814768094889/200000000000000000000000000000 : ℝ)*base68 + (156284634762719/12500000000000000000000000000 : ℝ)*base70 + (667684481494889/200000000000000000000000000000 : ℝ)*base72 + (380275898901607/200000000000000000000000000000 : ℝ)*base73 + (153996629487719/12500000000000000000000000000 : ℝ)*base76 + (44151053825219/12500000000000000000000000000 : ℝ)*base78 + (22298843562719/12500000000000000000000000000 : ℝ)*base80 + (3711107712281/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9232947/2500000000000000000000 : ℝ)*base89 + (9232947/2500000000000000000000 : ℝ)*base91 + (34232947/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1365_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (317/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_s1_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3954251/20000000 : ℝ)*x 0 + (563198007/1000000000 : ℝ)*x 1 + (5055170273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3954251/20000000 : ℝ)^4325 ≤ (2989494174703/25000000000000 : ℝ)^3301 := by
    have hnat : (3954251 : ℕ)^4325*25000000000000^3301 ≤ 2989494174703^3301*20000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3954251 20000000 2989494174703 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563198007/1000000000 : ℝ)^4325 ≤ (47131790053573/100000000000000 : ℝ)^3301 := by
    have hnat : (563198007 : ℕ)^4325*100000000000000^3301 ≤ 47131790053573^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563198007 1000000000 47131790053573 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5055170273/10000000000 : ℝ)^4325 ≤ (8182046648003/20000000000000 : ℝ)^3301 := by
    have hnat : (5055170273 : ℕ)^4325*20000000000000^3301 ≤ 8182046648003^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055170273 10000000000 8182046648003 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3954251/20000000 : ℝ), (563198007/1000000000 : ℝ), (5055170273/10000000000 : ℝ)] ![(2989494174703/25000000000000 : ℝ), (47131790053573/100000000000000 : ℝ), (8182046648003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3954251/20000000 : ℝ)|^4325 ≤ (2989494174703/25000000000000 : ℝ)^3301
        have hw : |(-3954251/20000000 : ℝ)|=(3954251/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563198007/1000000000 : ℝ)|^4325 ≤ (47131790053573/100000000000000 : ℝ)^3301
        have hw : |(563198007/1000000000 : ℝ)|=(563198007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5055170273/10000000000 : ℝ)|^4325 ≤ (8182046648003/20000000000000 : ℝ)^3301
        have hw : |(5055170273/10000000000 : ℝ)|=(5055170273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403332093/10000000000 : ℝ)*x 0 + (-2284328863/10000000000 : ℝ)*x 1 + (1011034273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403332093/10000000000 : ℝ)^4325 ≤ (8928137903923/20000000000000 : ℝ)^3301 := by
    have hnat : (5403332093 : ℕ)^4325*20000000000000^3301 ≤ 8928137903923^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403332093 10000000000 8928137903923 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284328863/10000000000 : ℝ)^4325 ≤ (14449065656617/100000000000000 : ℝ)^3301 := by
    have hnat : (2284328863 : ℕ)^4325*100000000000000^3301 ≤ 14449065656617^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284328863 10000000000 14449065656617 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011034273/2000000000 : ℝ)^4325 ≤ (2556890301169/6250000000000 : ℝ)^3301 := by
    have hnat : (1011034273 : ℕ)^4325*6250000000000^3301 ≤ 2556890301169^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011034273 2000000000 2556890301169 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403332093/10000000000 : ℝ), (-2284328863/10000000000 : ℝ), (1011034273/2000000000 : ℝ)] ![(8928137903923/20000000000000 : ℝ), (14449065656617/100000000000000 : ℝ), (2556890301169/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403332093/10000000000 : ℝ)|^4325 ≤ (8928137903923/20000000000000 : ℝ)^3301
        have hw : |(5403332093/10000000000 : ℝ)|=(5403332093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284328863/10000000000 : ℝ)|^4325 ≤ (14449065656617/100000000000000 : ℝ)^3301
        have hw : |(-2284328863/10000000000 : ℝ)|=(2284328863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011034273/2000000000 : ℝ)|^4325 ≤ (2556890301169/6250000000000 : ℝ)^3301
        have hw : |(1011034273/2000000000 : ℝ)|=(1011034273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350833097/2500000000 : ℝ)*x 0 + (1011034093/2000000000 : ℝ)*x 1 + (-2284329627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350833097/2500000000 : ℝ)^4325 ≤ (44640692712857/100000000000000 : ℝ)^3301 := by
    have hnat : (1350833097 : ℕ)^4325*100000000000000^3301 ≤ 44640692712857^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350833097 2500000000 44640692712857 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011034093/2000000000 : ℝ)^4325 ≤ (10227558818957/25000000000000 : ℝ)^3301 := by
    have hnat : (1011034093 : ℕ)^4325*25000000000000^3301 ≤ 10227558818957^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011034093 2000000000 10227558818957 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284329627/10000000000 : ℝ)^4325 ≤ (14449071988241/100000000000000 : ℝ)^3301 := by
    have hnat : (2284329627 : ℕ)^4325*100000000000000^3301 ≤ 14449071988241^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284329627 10000000000 14449071988241 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350833097/2500000000 : ℝ), (1011034093/2000000000 : ℝ), (-2284329627/10000000000 : ℝ)] ![(44640692712857/100000000000000 : ℝ), (10227558818957/25000000000000 : ℝ), (14449071988241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350833097/2500000000 : ℝ)|^4325 ≤ (44640692712857/100000000000000 : ℝ)^3301
        have hw : |(1350833097/2500000000 : ℝ)|=(1350833097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011034093/2000000000 : ℝ)|^4325 ≤ (10227558818957/25000000000000 : ℝ)^3301
        have hw : |(1011034093/2000000000 : ℝ)|=(1011034093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284329627/10000000000 : ℝ)|^4325 ≤ (14449071988241/100000000000000 : ℝ)^3301
        have hw : |(-2284329627/10000000000 : ℝ)|=(2284329627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34305551/80000000 : ℝ)*x 0 + (464824863/1250000000 : ℝ)*x 1 + (4937227433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34305551/80000000 : ℝ)^4325 ≤ (8244088092913/25000000000000 : ℝ)^3301 := by
    have hnat : (34305551 : ℕ)^4325*25000000000000^3301 ≤ 8244088092913^3301*80000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34305551 80000000 8244088092913 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464824863/1250000000 : ℝ)^4325 ≤ (3419929409107/12500000000000 : ℝ)^3301 := by
    have hnat : (464824863 : ℕ)^4325*12500000000000^3301 ≤ 3419929409107^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464824863 1250000000 3419929409107 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4937227433/10000000000 : ℝ)^4325 ≤ (4958026541453/12500000000000 : ℝ)^3301 := by
    have hnat : (4937227433 : ℕ)^4325*12500000000000^3301 ≤ 4958026541453^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4937227433 10000000000 4958026541453 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34305551/80000000 : ℝ), (464824863/1250000000 : ℝ), (4937227433/10000000000 : ℝ)] ![(8244088092913/25000000000000 : ℝ), (3419929409107/12500000000000 : ℝ), (4958026541453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34305551/80000000 : ℝ)|^4325 ≤ (8244088092913/25000000000000 : ℝ)^3301
        have hw : |(34305551/80000000 : ℝ)|=(34305551/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464824863/1250000000 : ℝ)|^4325 ≤ (3419929409107/12500000000000 : ℝ)^3301
        have hw : |(464824863/1250000000 : ℝ)|=(464824863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4937227433/10000000000 : ℝ)|^4325 ≤ (4958026541453/12500000000000 : ℝ)^3301
        have hw : |(4937227433/10000000000 : ℝ)|=(4937227433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-988810771/5000000000 : ℝ)*x 0 + (506228131/1000000000 : ℝ)*x 1 + (5624741973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988810771/5000000000 : ℝ)^4325 ≤ (2392381533169/20000000000000 : ℝ)^3301 := by
    have hnat : (988810771 : ℕ)^4325*20000000000000^3301 ≤ 2392381533169^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988810771 5000000000 2392381533169 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506228131/1000000000 : ℝ)^4325 ≤ (20492824699337/50000000000000 : ℝ)^3301 := by
    have hnat : (506228131 : ℕ)^4325*50000000000000^3301 ≤ 20492824699337^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506228131 1000000000 20492824699337 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5624741973/10000000000 : ℝ)^4325 ≤ (47052442926577/100000000000000 : ℝ)^3301 := by
    have hnat : (5624741973 : ℕ)^4325*100000000000000^3301 ≤ 47052442926577^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624741973 10000000000 47052442926577 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988810771/5000000000 : ℝ), (506228131/1000000000 : ℝ), (5624741973/10000000000 : ℝ)] ![(2392381533169/20000000000000 : ℝ), (20492824699337/50000000000000 : ℝ), (47052442926577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988810771/5000000000 : ℝ)|^4325 ≤ (2392381533169/20000000000000 : ℝ)^3301
        have hw : |(-988810771/5000000000 : ℝ)|=(988810771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506228131/1000000000 : ℝ)|^4325 ≤ (20492824699337/50000000000000 : ℝ)^3301
        have hw : |(506228131/1000000000 : ℝ)|=(506228131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5624741973/10000000000 : ℝ)|^4325 ≤ (47052442926577/100000000000000 : ℝ)^3301
        have hw : |(5624741973/10000000000 : ℝ)|=(5624741973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210134967/400000000 : ℝ)*x 0 + (-342951613/2000000000 : ℝ)*x 1 + (112494841/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210134967/400000000 : ℝ)^4325 ≤ (43024495100179/100000000000000 : ℝ)^3301 := by
    have hnat : (210134967 : ℕ)^4325*100000000000000^3301 ≤ 43024495100179^3301*400000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210134967 400000000 43024495100179 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342951613/2000000000 : ℝ)^4325 ≤ (2422622343/24414062500 : ℝ)^3301 := by
    have hnat : (342951613 : ℕ)^4325*24414062500^3301 ≤ 2422622343^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342951613 2000000000 2422622343 24414062500 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112494841/200000000 : ℝ)^4325 ≤ (11763110942629/25000000000000 : ℝ)^3301 := by
    have hnat : (112494841 : ℕ)^4325*25000000000000^3301 ≤ 11763110942629^3301*200000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112494841 200000000 11763110942629 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210134967/400000000 : ℝ), (-342951613/2000000000 : ℝ), (112494841/200000000 : ℝ)] ![(43024495100179/100000000000000 : ℝ), (2422622343/24414062500 : ℝ), (11763110942629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210134967/400000000 : ℝ)|^4325 ≤ (43024495100179/100000000000000 : ℝ)^3301
        have hw : |(210134967/400000000 : ℝ)|=(210134967/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342951613/2000000000 : ℝ)|^4325 ≤ (2422622343/24414062500 : ℝ)^3301
        have hw : |(-342951613/2000000000 : ℝ)|=(342951613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112494841/200000000 : ℝ)|^4325 ≤ (11763110942629/25000000000000 : ℝ)^3301
        have hw : |(112494841/200000000 : ℝ)|=(112494841/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313343517/2500000000 : ℝ)*x 0 + (2812371071/5000000000 : ℝ)*x 1 + (-1714758083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313343517/2500000000 : ℝ)^4325 ≤ (2151224697601/5000000000000 : ℝ)^3301 := by
    have hnat : (1313343517 : ℕ)^4325*5000000000000^3301 ≤ 2151224697601^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313343517 2500000000 2151224697601 5000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2812371071/5000000000 : ℝ)^4325 ≤ (23526222389429/50000000000000 : ℝ)^3301 := by
    have hnat : (2812371071 : ℕ)^4325*50000000000000^3301 ≤ 23526222389429^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812371071 5000000000 23526222389429 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714758083/10000000000 : ℝ)^4325 ≤ (2480765313351/25000000000000 : ℝ)^3301 := by
    have hnat : (1714758083 : ℕ)^4325*25000000000000^3301 ≤ 2480765313351^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714758083 10000000000 2480765313351 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313343517/2500000000 : ℝ), (2812371071/5000000000 : ℝ), (-1714758083/10000000000 : ℝ)] ![(2151224697601/5000000000000 : ℝ), (23526222389429/50000000000000 : ℝ), (2480765313351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313343517/2500000000 : ℝ)|^4325 ≤ (2151224697601/5000000000000 : ℝ)^3301
        have hw : |(1313343517/2500000000 : ℝ)|=(1313343517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2812371071/5000000000 : ℝ)|^4325 ≤ (23526222389429/50000000000000 : ℝ)^3301
        have hw : |(2812371071/5000000000 : ℝ)|=(2812371071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714758083/10000000000 : ℝ)|^4325 ≤ (2480765313351/25000000000000 : ℝ)^3301
        have hw : |(-1714758083/10000000000 : ℝ)|=(1714758083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s1_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536155321/1250000000 : ℝ)*x 0 + (307637847/625000000 : ℝ)*x 1 + (1866943931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536155321/1250000000 : ℝ)^4325 ≤ (32986918931853/100000000000000 : ℝ)^3301 := by
    have hnat : (536155321 : ℕ)^4325*100000000000000^3301 ≤ 32986918931853^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536155321 1250000000 32986918931853 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307637847/625000000 : ℝ)^4325 ≤ (39506169259667/100000000000000 : ℝ)^3301 := by
    have hnat : (307637847 : ℕ)^4325*100000000000000^3301 ≤ 39506169259667^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307637847 625000000 39506169259667 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866943931/5000000000 : ℝ)^4325 ≤ (5501382357911/20000000000000 : ℝ)^3301 := by
    have hnat : (1866943931 : ℕ)^4325*20000000000000^3301 ≤ 5501382357911^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866943931 5000000000 5501382357911 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536155321/1250000000 : ℝ), (307637847/625000000 : ℝ), (1866943931/5000000000 : ℝ)] ![(32986918931853/100000000000000 : ℝ), (39506169259667/100000000000000 : ℝ), (5501382357911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536155321/1250000000 : ℝ)|^4325 ≤ (32986918931853/100000000000000 : ℝ)^3301
        have hw : |(536155321/1250000000 : ℝ)|=(536155321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307637847/625000000 : ℝ)|^4325 ≤ (39506169259667/100000000000000 : ℝ)^3301
        have hw : |(307637847/625000000 : ℝ)|=(307637847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1866943931/5000000000 : ℝ)|^4325 ≤ (5501382357911/20000000000000 : ℝ)^3301
        have hw : |(1866943931/5000000000 : ℝ)|=(1866943931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (71/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4823/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (317/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (317/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (317/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (317/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (317/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (317/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (317/20000 : ℝ) ^ (1081/256 : ℝ) ≤ (1254042736129/50000000000000000000 : ℝ) := by
    have hpowers : (317/20000 : ℝ)^1081 ≤ (1254042736129/50000000000000000000 : ℝ)^256 := by
      have hnat : (317 : ℕ)^1081*50000000000000000000^256 ≤ 1254042736129^256*20000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 20000 1254042736129 50000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/20000 : ℝ)) (X := (1254042736129/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26707/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (379170832437409613/100000000000000000000 : ℝ) := by
    have hpowers : (26707/100000 : ℝ)^1081 ≤ (379170832437409613/100000000000000000000 : ℝ)^256 := by
      have hnat : (26707 : ℕ)^1081*100000000000000000000^256 ≤ 379170832437409613^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26707 100000 379170832437409613 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26707/100000 : ℝ)) (X := (379170832437409613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001254042736129/25000000000000000000 : ℝ) ≤ (2500000029697959/2500000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (25000001254042736129/25000000000000000000 : ℝ)^256 ≤ (2500000029697959/2500000000000000 : ℝ)^1081 := by
      have hnat : (25000001254042736129 : ℕ)^256*2500000000000000^1081 ≤ 2500000029697959^1081*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001254042736129 25000000000000000000 2500000029697959 2500000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000029697959/2500000000000000 : ℝ)) (X := (25000001254042736129/25000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100379173340522881871/100000000000000000000 : ℝ) ≤ (5004483267340831/5000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (100379173340522881871/100000000000000000000 : ℝ)^256 ≤ (5004483267340831/5000000000000000 : ℝ)^1081 := by
      have hnat : (100379173340522881871 : ℕ)^256*5000000000000000^1081 ≤ 5004483267340831^1081*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100379173340522881871 100000000000000000000 5004483267340831 5000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004483267340831/5000000000000000 : ℝ)) (X := (100379173340522881871/100000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50379170832437409613/50000000000000000000 : ℝ) ≤ (313060404705359/312500000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50379170832437409613/50000000000000000000 : ℝ)^256 ≤ (313060404705359/312500000000000 : ℝ)^1081 := by
      have hnat : (50379170832437409613 : ℕ)^256*312500000000000^1081 ≤ 313060404705359^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50379170832437409613 50000000000000000000 313060404705359 312500000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313060404705359/312500000000000 : ℝ)) (X := (50379170832437409613/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1254042736129/50000000000000000000 : ℝ) ≤ ((62797894861479438893/62805000000000000000 : ℝ)+2*(4483207944913/1256100000000000 : ℝ)*(317/20000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (62797894861479438893/62805000000000000000 : ℝ)+2*(4483207944913/1256100000000000 : ℝ)*(317/20000 : ℝ)=(2500000029697959/2500000000000000 : ℝ) by norm_num, show 1+2*(1254042736129/50000000000000000000 : ℝ)=(25000001254042736129/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(379170832437409613/100000000000000000000 : ℝ)+(1254042736129/50000000000000000000 : ℝ) ≤ ((62797894861479438893/62805000000000000000 : ℝ)+(4483207944913/1256100000000000 : ℝ)*((26707/100000 : ℝ)+(317/20000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (62797894861479438893/62805000000000000000 : ℝ)+(4483207944913/1256100000000000 : ℝ)*((26707/100000 : ℝ)+(317/20000 : ℝ))=(5004483267340831/5000000000000000 : ℝ) by norm_num, show 1+(379170832437409613/100000000000000000000 : ℝ)+(1254042736129/50000000000000000000 : ℝ)=(100379173340522881871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(379170832437409613/100000000000000000000 : ℝ) ≤ ((62797894861479438893/62805000000000000000 : ℝ)+2*(4483207944913/1256100000000000 : ℝ)*(26707/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (62797894861479438893/62805000000000000000 : ℝ)+2*(4483207944913/1256100000000000 : ℝ)*(26707/100000 : ℝ)=(313060404705359/312500000000000 : ℝ) by norm_num, show 1+2*(379170832437409613/100000000000000000000 : ℝ)=(50379170832437409613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62797894861479438893/62805000000000000000 : ℝ)*(X 1 0+X 2 0)+(4483207944913/1256100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (317/20000 : ℝ)) (hi := (26707/100000 : ℝ)) (c := (62797894861479438893/62805000000000000000 : ℝ)) (alpha := (4483207944913/1256100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62797894861479438893/62805000000000000000 : ℝ)*(X 0 1+X 2 1)+(4483207944913/1256100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (317/20000 : ℝ)) (hi := (26707/100000 : ℝ)) (c := (62797894861479438893/62805000000000000000 : ℝ)) (alpha := (4483207944913/1256100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62797894861479438893/62805000000000000000 : ℝ)*(X 0 2+X 1 2)+(4483207944913/1256100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (317/20000 : ℝ)) (hi := (26707/100000 : ℝ)) (c := (62797894861479438893/62805000000000000000 : ℝ)) (alpha := (4483207944913/1256100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3954251/20000000 : ℝ)*X 0 0+(563198007/1000000000 : ℝ)*X 0 1+(5055170273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403332093/10000000000 : ℝ)*X 1 0+(-2284328863/10000000000 : ℝ)*X 1 1+(1011034273/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350833097/2500000000 : ℝ)*X 2 0+(1011034093/2000000000 : ℝ)*X 2 1+(-2284329627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34305551/80000000 : ℝ)*X 0 0+(464824863/1250000000 : ℝ)*X 0 1+(4937227433/10000000000 : ℝ)*X 0 2+(34305551/80000000 : ℝ)*X 1 0+(464824863/1250000000 : ℝ)*X 1 1+(4937227433/10000000000 : ℝ)*X 1 2+(34305551/80000000 : ℝ)*X 2 0+(464824863/1250000000 : ℝ)*X 2 1+(4937227433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-988810771/5000000000 : ℝ)*X 0 0+(506228131/1000000000 : ℝ)*X 0 1+(5624741973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210134967/400000000 : ℝ)*X 1 0+(-342951613/2000000000 : ℝ)*X 1 1+(112494841/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313343517/2500000000 : ℝ)*X 2 0+(2812371071/5000000000 : ℝ)*X 2 1+(-1714758083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((536155321/1250000000 : ℝ)*X 0 0+(307637847/625000000 : ℝ)*X 0 1+(1866943931/5000000000 : ℝ)*X 0 2+(536155321/1250000000 : ℝ)*X 1 0+(307637847/625000000 : ℝ)*X 1 1+(1866943931/5000000000 : ℝ)*X 1 2+(536155321/1250000000 : ℝ)*X 2 0+(307637847/625000000 : ℝ)*X 2 1+(1866943931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7419195995298469394681726623/1046750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16040563/50000000000000 : ℝ)*(base16) + (207186353/20000000000000 : ℝ)*(base19) + (1183194347/100000000000000 : ℝ)*(base23) + (11092459/100000000000000 : ℝ)*(upper2) + (7859961/4000000000000 : ℝ)*(upper3) + (1277146946508389/100000000000000 : ℝ)*(major0) + (1277146946508389/100000000000000 : ℝ)*(major1) + (1277146946508389/100000000000000 : ℝ)*(major2) + (1733684357879659/100000000000000 : ℝ)*(sp0) + (216711484085961/12500000000000 : ℝ)*(sp1) + (1733691757506231/100000000000000 : ℝ)*(sp2) + (102574639357851/12500000000000 : ℝ)*(sp3) + (8582820919/100000000000000 : ℝ)*(sp4) + (900298017/25000000000000 : ℝ)*(sp7) + (205150179013719/25000000000000 : ℝ)*(f.failure) + (866846470350289/50000000000000 : ℝ)*(f.sum) + (157131406692227/62805000000000000000000000000 : ℝ)*base65 + (29157000493361223377/6280500000000000000000000000000000 : ℝ)*base67 + (44045826454988223377/6280500000000000000000000000000000 : ℝ)*base69 + (10104782929548776623/6280500000000000000000000000000000 : ℝ)*base72 + (425536412381837/62805000000000000000000000000 : ℝ)*base73 + (22751963900304776623/6280500000000000000000000000000000 : ℝ)*base76 + (19176549516809223377/6280500000000000000000000000000000 : ℝ)*base77 + (37148639079063723377/6280500000000000000000000000000000 : ℝ)*base79 + (142724948185771/31402500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3009743/625000000000000000000 : ℝ)*base90 + (3009743/625000000000000000000 : ℝ)*base92 + (3009743/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9056974334888312130979676733/1046750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18073149/20000000000000 : ℝ)*(base1) + (875498413/50000000000000 : ℝ)*(base19) + (8572829/500000000000 : ℝ)*(base23) + (203663311/100000000000000 : ℝ)*(upper3) + (48134213/25000000000000 : ℝ)*(upper5) + (1309714004234881/100000000000000 : ℝ)*(major0) + (1309714004234881/100000000000000 : ℝ)*(major1) + (1309714004234881/100000000000000 : ℝ)*(major2) + (4611406671/50000000000000 : ℝ)*(sp1) + (4607558253/50000000000000 : ℝ)*(sp2) + (355580379561223/20000000000000 : ℝ)*(sp4) + (1777890833630201/100000000000000 : ℝ)*(sp5) + (111118179859879/6250000000000 : ℝ)*(sp6) + (841525822247931/100000000000000 : ℝ)*(sp7) + (841525912613677/100000000000000 : ℝ)*(f.failure) + (177790180744037/10000000000000 : ℝ)*(f.sum) + (59972420504563/62805000000000000000000000000 : ℝ)*base65 + (22244377015964723267/6280500000000000000000000000000000 : ℝ)*base68 + (8216596732792223267/6280500000000000000000000000000000 : ℝ)*base70 + (23373738124861776733/6280500000000000000000000000000000 : ℝ)*base71 + (23690088402619/7850625000000000000000000000 : ℝ)*base74 + (21449728221915276733/6280500000000000000000000000000000 : ℝ)*base75 + (35964656363207723267/6280500000000000000000000000000000 : ℝ)*base78 + (20725235406668723267/6280500000000000000000000000000000 : ℝ)*base80 + (34785343618787/62805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9866331/2500000000000000000000 : ℝ)*base89 + (9866331/2500000000000000000000 : ℝ)*base91 + (9866331/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1365_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4823/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_s2_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-125957393/625000000 : ℝ)*x 0 + (2736813069/5000000000 : ℝ)*x 1 + (2594513931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125957393/625000000 : ℝ)^4325 ≤ (12261532815993/100000000000000 : ℝ)^3301 := by
    have hnat : (125957393 : ℕ)^4325*100000000000000^3301 ≤ 12261532815993^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125957393 625000000 12261532815993 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736813069/5000000000 : ℝ)^4325 ≤ (45403121662819/100000000000000 : ℝ)^3301 := by
    have hnat : (2736813069 : ℕ)^4325*100000000000000^3301 ≤ 45403121662819^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736813069 5000000000 45403121662819 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594513931/5000000000 : ℝ)^4325 ≤ (4233534551173/10000000000000 : ℝ)^3301 := by
    have hnat : (2594513931 : ℕ)^4325*10000000000000^3301 ≤ 4233534551173^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594513931 5000000000 4233534551173 10000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125957393/625000000 : ℝ), (2736813069/5000000000 : ℝ), (2594513931/5000000000 : ℝ)] ![(12261532815993/100000000000000 : ℝ), (45403121662819/100000000000000 : ℝ), (4233534551173/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125957393/625000000 : ℝ)|^4325 ≤ (12261532815993/100000000000000 : ℝ)^3301
        have hw : |(-125957393/625000000 : ℝ)|=(125957393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736813069/5000000000 : ℝ)|^4325 ≤ (45403121662819/100000000000000 : ℝ)^3301
        have hw : |(2736813069/5000000000 : ℝ)|=(2736813069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594513931/5000000000 : ℝ)|^4325 ≤ (4233534551173/10000000000000 : ℝ)^3301
        have hw : |(2594513931/5000000000 : ℝ)|=(2594513931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364358511/10000000000 : ℝ)*x 0 + (-2162192009/10000000000 : ℝ)*x 1 + (2594514077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364358511/10000000000 : ℝ)^4325 ≤ (44219290815327/100000000000000 : ℝ)^3301 := by
    have hnat : (5364358511 : ℕ)^4325*100000000000000^3301 ≤ 44219290815327^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364358511 10000000000 44219290815327 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162192009/10000000000 : ℝ)^4325 ≤ (13445360542419/100000000000000 : ℝ)^3301 := by
    have hnat : (2162192009 : ℕ)^4325*100000000000000^3301 ≤ 13445360542419^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162192009 10000000000 13445360542419 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594514077/5000000000 : ℝ)^4325 ≤ (21167674316533/50000000000000 : ℝ)^3301 := by
    have hnat : (2594514077 : ℕ)^4325*50000000000000^3301 ≤ 21167674316533^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594514077 5000000000 21167674316533 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364358511/10000000000 : ℝ), (-2162192009/10000000000 : ℝ), (2594514077/5000000000 : ℝ)] ![(44219290815327/100000000000000 : ℝ), (13445360542419/100000000000000 : ℝ), (21167674316533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364358511/10000000000 : ℝ)|^4325 ≤ (44219290815327/100000000000000 : ℝ)^3301
        have hw : |(5364358511/10000000000 : ℝ)|=(5364358511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2162192009/10000000000 : ℝ)|^4325 ≤ (13445360542419/100000000000000 : ℝ)^3301
        have hw : |(-2162192009/10000000000 : ℝ)|=(2162192009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594514077/5000000000 : ℝ)|^4325 ≤ (21167674316533/50000000000000 : ℝ)^3301
        have hw : |(2594514077/5000000000 : ℝ)|=(2594514077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364358541/10000000000 : ℝ)*x 0 + (518902811/1000000000 : ℝ)*x 1 + (-2162192027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364358541/10000000000 : ℝ)^4325 ≤ (8843858227867/20000000000000 : ℝ)^3301 := by
    have hnat : (5364358541 : ℕ)^4325*20000000000000^3301 ≤ 8843858227867^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364358541 10000000000 8843858227867 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518902811/1000000000 : ℝ)^4325 ≤ (5291918520341/12500000000000 : ℝ)^3301 := by
    have hnat : (518902811 : ℕ)^4325*12500000000000^3301 ≤ 5291918520341^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518902811 1000000000 5291918520341 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162192027/10000000000 : ℝ)^4325 ≤ (840335043067/6250000000000 : ℝ)^3301 := by
    have hnat : (2162192027 : ℕ)^4325*6250000000000^3301 ≤ 840335043067^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162192027 10000000000 840335043067 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364358541/10000000000 : ℝ), (518902811/1000000000 : ℝ), (-2162192027/10000000000 : ℝ)] ![(8843858227867/20000000000000 : ℝ), (5291918520341/12500000000000 : ℝ), (840335043067/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364358541/10000000000 : ℝ)|^4325 ≤ (8843858227867/20000000000000 : ℝ)^3301
        have hw : |(5364358541/10000000000 : ℝ)|=(5364358541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518902811/1000000000 : ℝ)|^4325 ≤ (5291918520341/12500000000000 : ℝ)^3301
        have hw : |(518902811/1000000000 : ℝ)|=(518902811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2162192027/10000000000 : ℝ)|^4325 ≤ (840335043067/6250000000000 : ℝ)^3301
        have hw : |(-2162192027/10000000000 : ℝ)|=(2162192027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314972357/10000000000 : ℝ)*x 0 + (4024000941/10000000000 : ℝ)*x 1 + (2312637247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314972357/10000000000 : ℝ)^4325 ≤ (519475332499/1562500000000 : ℝ)^3301 := by
    have hnat : (4314972357 : ℕ)^4325*1562500000000^3301 ≤ 519475332499^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314972357 10000000000 519475332499 1562500000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024000941/10000000000 : ℝ)^4325 ≤ (30340269844967/100000000000000 : ℝ)^3301 := by
    have hnat : (4024000941 : ℕ)^4325*100000000000000^3301 ≤ 30340269844967^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024000941 10000000000 30340269844967 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312637247/5000000000 : ℝ)^4325 ≤ (7282661771847/20000000000000 : ℝ)^3301 := by
    have hnat : (2312637247 : ℕ)^4325*20000000000000^3301 ≤ 7282661771847^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312637247 5000000000 7282661771847 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314972357/10000000000 : ℝ), (4024000941/10000000000 : ℝ), (2312637247/5000000000 : ℝ)] ![(519475332499/1562500000000 : ℝ), (30340269844967/100000000000000 : ℝ), (7282661771847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314972357/10000000000 : ℝ)|^4325 ≤ (519475332499/1562500000000 : ℝ)^3301
        have hw : |(4314972357/10000000000 : ℝ)|=(4314972357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024000941/10000000000 : ℝ)|^4325 ≤ (30340269844967/100000000000000 : ℝ)^3301
        have hw : |(4024000941/10000000000 : ℝ)|=(4024000941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312637247/5000000000 : ℝ)|^4325 ≤ (7282661771847/20000000000000 : ℝ)^3301
        have hw : |(2312637247/5000000000 : ℝ)|=(2312637247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007688961/5000000000 : ℝ)*x 0 + (129769219/250000000 : ℝ)*x 1 + (34199187/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007688961/5000000000 : ℝ)^4325 ≤ (6131004096209/50000000000000 : ℝ)^3301 := by
    have hnat : (1007688961 : ℕ)^4325*50000000000000^3301 ≤ 6131004096209^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007688961 5000000000 6131004096209 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129769219/250000000 : ℝ)^4325 ≤ (42353955822131/100000000000000 : ℝ)^3301 := by
    have hnat : (129769219 : ℕ)^4325*100000000000000^3301 ≤ 42353955822131^3301*250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129769219 250000000 42353955822131 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34199187/62500000 : ℝ)^4325 ≤ (5673004495977/12500000000000 : ℝ)^3301 := by
    have hnat : (34199187 : ℕ)^4325*12500000000000^3301 ≤ 5673004495977^3301*62500000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34199187 62500000 5673004495977 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007688961/5000000000 : ℝ), (129769219/250000000 : ℝ), (34199187/62500000 : ℝ)] ![(6131004096209/50000000000000 : ℝ), (42353955822131/100000000000000 : ℝ), (5673004495977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007688961/5000000000 : ℝ)|^4325 ≤ (6131004096209/50000000000000 : ℝ)^3301
        have hw : |(-1007688961/5000000000 : ℝ)|=(1007688961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129769219/250000000 : ℝ)|^4325 ≤ (42353955822131/100000000000000 : ℝ)^3301
        have hw : |(129769219/250000000 : ℝ)|=(129769219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34199187/62500000 : ℝ)|^4325 ≤ (5673004495977/12500000000000 : ℝ)^3301
        have hw : |(34199187/62500000 : ℝ)|=(34199187/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290823233/10000000000 : ℝ)*x 0 + (-187934997/1000000000 : ℝ)*x 1 + (683983733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290823233/10000000000 : ℝ)^4325 ≤ (21713392010413/50000000000000 : ℝ)^3301 := by
    have hnat : (5290823233 : ℕ)^4325*50000000000000^3301 ≤ 21713392010413^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290823233 10000000000 21713392010413 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187934997/1000000000 : ℝ)^4325 ≤ (11189180607589/100000000000000 : ℝ)^3301 := by
    have hnat : (187934997 : ℕ)^4325*100000000000000^3301 ≤ 11189180607589^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187934997 1000000000 11189180607589 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683983733/1250000000 : ℝ)^4325 ≤ (22692017679633/50000000000000 : ℝ)^3301 := by
    have hnat : (683983733 : ℕ)^4325*50000000000000^3301 ≤ 22692017679633^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683983733 1250000000 22692017679633 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290823233/10000000000 : ℝ), (-187934997/1000000000 : ℝ), (683983733/1250000000 : ℝ)] ![(21713392010413/50000000000000 : ℝ), (11189180607589/100000000000000 : ℝ), (22692017679633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290823233/10000000000 : ℝ)|^4325 ≤ (21713392010413/50000000000000 : ℝ)^3301
        have hw : |(5290823233/10000000000 : ℝ)|=(5290823233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187934997/1000000000 : ℝ)|^4325 ≤ (11189180607589/100000000000000 : ℝ)^3301
        have hw : |(-187934997/1000000000 : ℝ)|=(187934997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683983733/1250000000 : ℝ)|^4325 ≤ (22692017679633/50000000000000 : ℝ)^3301
        have hw : |(683983733/1250000000 : ℝ)|=(683983733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290823191/10000000000 : ℝ)*x 0 + (5471869923/10000000000 : ℝ)*x 1 + (-375869989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290823191/10000000000 : ℝ)^4325 ≤ (43426783569153/100000000000000 : ℝ)^3301 := by
    have hnat : (5290823191 : ℕ)^4325*100000000000000^3301 ≤ 43426783569153^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290823191 10000000000 43426783569153 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471869923/10000000000 : ℝ)^4325 ≤ (45384036000417/100000000000000 : ℝ)^3301 := by
    have hnat : (5471869923 : ℕ)^4325*100000000000000^3301 ≤ 45384036000417^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471869923 10000000000 45384036000417 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375869989/2000000000 : ℝ)^4325 ≤ (2797295103143/25000000000000 : ℝ)^3301 := by
    have hnat : (375869989 : ℕ)^4325*25000000000000^3301 ≤ 2797295103143^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375869989 2000000000 2797295103143 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290823191/10000000000 : ℝ), (5471869923/10000000000 : ℝ), (-375869989/2000000000 : ℝ)] ![(43426783569153/100000000000000 : ℝ), (45384036000417/100000000000000 : ℝ), (2797295103143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290823191/10000000000 : ℝ)|^4325 ≤ (43426783569153/100000000000000 : ℝ)^3301
        have hw : |(5290823191/10000000000 : ℝ)|=(5290823191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471869923/10000000000 : ℝ)|^4325 ≤ (45384036000417/100000000000000 : ℝ)^3301
        have hw : |(5471869923/10000000000 : ℝ)|=(5471869923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375869989/2000000000 : ℝ)|^4325 ≤ (2797295103143/25000000000000 : ℝ)^3301
        have hw : |(-375869989/2000000000 : ℝ)|=(375869989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s2_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863019719/2000000000 : ℝ)*x 0 + (4621596981/10000000000 : ℝ)*x 1 + (1006927699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863019719/2000000000 : ℝ)^4325 ≤ (33247695661703/100000000000000 : ℝ)^3301 := by
    have hnat : (863019719 : ℕ)^4325*100000000000000^3301 ≤ 33247695661703^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863019719 2000000000 33247695661703 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4621596981/10000000000 : ℝ)^4325 ≤ (36375380516567/100000000000000 : ℝ)^3301 := by
    have hnat : (4621596981 : ℕ)^4325*100000000000000^3301 ≤ 36375380516567^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4621596981 10000000000 36375380516567 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006927699/2500000000 : ℝ)^4325 ≤ (15188461905503/50000000000000 : ℝ)^3301 := by
    have hnat : (1006927699 : ℕ)^4325*50000000000000^3301 ≤ 15188461905503^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006927699 2500000000 15188461905503 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863019719/2000000000 : ℝ), (4621596981/10000000000 : ℝ), (1006927699/2500000000 : ℝ)] ![(33247695661703/100000000000000 : ℝ), (36375380516567/100000000000000 : ℝ), (15188461905503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863019719/2000000000 : ℝ)|^4325 ≤ (33247695661703/100000000000000 : ℝ)^3301
        have hw : |(863019719/2000000000 : ℝ)|=(863019719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4621596981/10000000000 : ℝ)|^4325 ≤ (36375380516567/100000000000000 : ℝ)^3301
        have hw : |(4621596981/10000000000 : ℝ)|=(4621596981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006927699/2500000000 : ℝ)|^4325 ≤ (15188461905503/50000000000000 : ℝ)^3301
        have hw : |(1006927699/2500000000 : ℝ)|=(1006927699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4823/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (4999/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1001/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4823/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4823/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4823/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4823/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4823/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4823/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/1000 : ℝ) ^ (1081/256 : ℝ) ≤ (1410129137736717/100000000000000000000 : ℝ) := by
    have hpowers : (71/1000 : ℝ)^1081 ≤ (1410129137736717/100000000000000000000 : ℝ)^256 := by
      have hnat : (71 : ℕ)^1081*100000000000000000000^256 ≤ 1410129137736717^256*1000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 1000 1410129137736717 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/1000 : ℝ)) (X := (1410129137736717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4823/25000 : ℝ) ^ (1081/256 : ℝ) ≤ (19205419053271009/20000000000000000000 : ℝ) := by
    have hpowers : (4823/25000 : ℝ)^1081 ≤ (19205419053271009/20000000000000000000 : ℝ)^256 := by
      have hnat : (4823 : ℕ)^1081*20000000000000000000^256 ≤ 19205419053271009^256*25000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4823 25000 19205419053271009 20000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4823/25000 : ℝ)) (X := (19205419053271009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001410129137736717/50000000000000000000 : ℝ) ≤ (10000066788006359/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50001410129137736717/50000000000000000000 : ℝ)^256 ≤ (10000066788006359/10000000000000000 : ℝ)^1081 := by
      have hnat : (50001410129137736717 : ℕ)^256*10000000000000000^1081 ≤ 10000066788006359^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001410129137736717 50000000000000000000 10000066788006359 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000066788006359/10000000000000000 : ℝ)) (X := (50001410129137736717/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50048718612202045881/50000000000000000000 : ℝ) ≤ (1250288328634457/1250000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50048718612202045881/50000000000000000000 : ℝ)^256 ≤ (1250288328634457/1250000000000000 : ℝ)^1081 := by
      have hnat : (50048718612202045881 : ℕ)^256*1250000000000000^1081 ≤ 1250288328634457^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048718612202045881 50000000000000000000 1250288328634457 1250000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250288328634457/1250000000000000 : ℝ)) (X := (50048718612202045881/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10019205419053271009/10000000000000000000 : ℝ) ≤ (10004546470144953/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (10019205419053271009/10000000000000000000 : ℝ)^256 ≤ (10004546470144953/10000000000000000 : ℝ)^1081 := by
      have hnat : (10019205419053271009 : ℕ)^256*10000000000000000^1081 ≤ 10004546470144953^1081*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10019205419053271009 10000000000000000000 10004546470144953 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004546470144953/10000000000000000 : ℝ)) (X := (10019205419053271009/10000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1410129137736717/100000000000000000000 : ℝ) ≤ ((15236126067023688941/15240000000000000000 : ℝ)+2*(2239841069297/1219200000000000 : ℝ)*(71/1000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (15236126067023688941/15240000000000000000 : ℝ)+2*(2239841069297/1219200000000000 : ℝ)*(71/1000 : ℝ)=(10000066788006359/10000000000000000 : ℝ) by norm_num, show 1+2*(1410129137736717/100000000000000000000 : ℝ)=(50001410129137736717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19205419053271009/20000000000000000000 : ℝ)+(1410129137736717/100000000000000000000 : ℝ) ≤ ((15236126067023688941/15240000000000000000 : ℝ)+(2239841069297/1219200000000000 : ℝ)*((4823/25000 : ℝ)+(71/1000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (15236126067023688941/15240000000000000000 : ℝ)+(2239841069297/1219200000000000 : ℝ)*((4823/25000 : ℝ)+(71/1000 : ℝ))=(1250288328634457/1250000000000000 : ℝ) by norm_num, show 1+(19205419053271009/20000000000000000000 : ℝ)+(1410129137736717/100000000000000000000 : ℝ)=(50048718612202045881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19205419053271009/20000000000000000000 : ℝ) ≤ ((15236126067023688941/15240000000000000000 : ℝ)+2*(2239841069297/1219200000000000 : ℝ)*(4823/25000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (15236126067023688941/15240000000000000000 : ℝ)+2*(2239841069297/1219200000000000 : ℝ)*(4823/25000 : ℝ)=(10004546470144953/10000000000000000 : ℝ) by norm_num, show 1+2*(19205419053271009/20000000000000000000 : ℝ)=(10019205419053271009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15236126067023688941/15240000000000000000 : ℝ)*(X 1 0+X 2 0)+(2239841069297/1219200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (71/1000 : ℝ)) (hi := (4823/25000 : ℝ)) (c := (15236126067023688941/15240000000000000000 : ℝ)) (alpha := (2239841069297/1219200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15236126067023688941/15240000000000000000 : ℝ)*(X 0 1+X 2 1)+(2239841069297/1219200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (71/1000 : ℝ)) (hi := (4823/25000 : ℝ)) (c := (15236126067023688941/15240000000000000000 : ℝ)) (alpha := (2239841069297/1219200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15236126067023688941/15240000000000000000 : ℝ)*(X 0 2+X 1 2)+(2239841069297/1219200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (71/1000 : ℝ)) (hi := (4823/25000 : ℝ)) (c := (15236126067023688941/15240000000000000000 : ℝ)) (alpha := (2239841069297/1219200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-125957393/625000000 : ℝ)*X 0 0+(2736813069/5000000000 : ℝ)*X 0 1+(2594513931/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364358511/10000000000 : ℝ)*X 1 0+(-2162192009/10000000000 : ℝ)*X 1 1+(2594514077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364358541/10000000000 : ℝ)*X 2 0+(518902811/1000000000 : ℝ)*X 2 1+(-2162192027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314972357/10000000000 : ℝ)*X 0 0+(4024000941/10000000000 : ℝ)*X 0 1+(2312637247/5000000000 : ℝ)*X 0 2+(4314972357/10000000000 : ℝ)*X 1 0+(4024000941/10000000000 : ℝ)*X 1 1+(2312637247/5000000000 : ℝ)*X 1 2+(4314972357/10000000000 : ℝ)*X 2 0+(4024000941/10000000000 : ℝ)*X 2 1+(2312637247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1007688961/5000000000 : ℝ)*X 0 0+(129769219/250000000 : ℝ)*X 0 1+(34199187/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290823233/10000000000 : ℝ)*X 1 0+(-187934997/1000000000 : ℝ)*X 1 1+(683983733/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290823191/10000000000 : ℝ)*X 2 0+(5471869923/10000000000 : ℝ)*X 2 1+(-375869989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863019719/2000000000 : ℝ)*X 0 0+(4621596981/10000000000 : ℝ)*X 0 1+(1006927699/2500000000 : ℝ)*X 0 2+(863019719/2000000000 : ℝ)*X 1 0+(4621596981/10000000000 : ℝ)*X 1 1+(1006927699/2500000000 : ℝ)*X 1 2+(863019719/2000000000 : ℝ)*X 2 0+(4621596981/10000000000 : ℝ)*X 2 1+(1006927699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59219282341746261392554221/6350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1607787789/100000000000000 : ℝ)*(base19) + (776832829/50000000000000 : ℝ)*(base23) + (19787181/50000000000000 : ℝ)*(lower2) + (225162713/100000000000000 : ℝ)*(upper3) + (154889823/100000000000000 : ℝ)*(upper5) + (64711607849919/2500000000000 : ℝ)*(major0) + (64711607849919/2500000000000 : ℝ)*(major1) + (64711607849919/2500000000000 : ℝ)*(major2) + (1756874235410567/50000000000000 : ℝ)*(sp0) + (439221234668421/12500000000000 : ℝ)*(sp1) + (3513769931469499/100000000000000 : ℝ)*(sp2) + (51973317884647/3125000000000 : ℝ)*(sp3) + (11507157011/50000000000000 : ℝ)*(sp4) + (10659687279/100000000000000 : ℝ)*(sp7) + (1663156831995983/100000000000000 : ℝ)*(f.failure) + (3513771485135157/100000000000000 : ℝ)*(f.sum) + (50433609167/20320000000000000000000000 : ℝ)*base66 + (10166592414111093/12700000000000000000000000000000 : ℝ)*base67 + (102060423955011093/12700000000000000000000000000000 : ℝ)*base69 + (94416243962088907/12700000000000000000000000000000 : ℝ)*base72 + (813985849327/508000000000000000000000000 : ℝ)*base74 + (170267743420211093/12700000000000000000000000000000 : ℝ)*base75 + (7089878768211093/12700000000000000000000000000000 : ℝ)*base77 + (69917876296488907/12700000000000000000000000000000 : ℝ)*base80 + (312298396477/101600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1063351/2500000000000000000000 : ℝ)*base90 + (1063351/2500000000000000000000 : ℝ)*base92 + (1063351/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27424261908809950983493389/3968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181844349/12500000000000 : ℝ)*(base19) + (1585331033/100000000000000 : ℝ)*(base23) + (161750269/100000000000000 : ℝ)*(upper3) + (16227249/25000000000000 : ℝ)*(lower4) + (114510683/100000000000000 : ℝ)*(upper5) + (40947351067371/1562500000000 : ℝ)*(major0) + (40947351067371/1562500000000 : ℝ)*(major1) + (40947351067371/1562500000000 : ℝ)*(major2) + (674667097/4000000000000 : ℝ)*(sp1) + (1946647317/10000000000000 : ℝ)*(sp2) + (1778718134393253/50000000000000 : ℝ)*(sp4) + (355741794735429/10000000000000 : ℝ)*(sp5) + (111169225530697/3125000000000 : ℝ)*(sp6) + (1683824437501967/100000000000000 : ℝ)*(sp7) + (1683824437501967/100000000000000 : ℝ)*(f.failure) + (1778718134393253/50000000000000 : ℝ)*(f.sum) + (3910788148497/635000000000000000000000000 : ℝ)*base66 + (43123999754348037/7937500000000000000000000000000 : ℝ)*base67 + (35277613800910537/7937500000000000000000000000000 : ℝ)*base69 + (1470730865535537/7937500000000000000000000000000 : ℝ)*base71 + (346598941461/79375000000000000000000000 : ℝ)*base73 + (73148957588464463/7937500000000000000000000000000 : ℝ)*base76 + (15979502259098037/7937500000000000000000000000000 : ℝ)*base77 + (46707058930901963/7937500000000000000000000000000 : ℝ)*base80 + (265386143511/79375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3687799/2500000000000000000000 : ℝ)*base90 + (3687799/2500000000000000000000 : ℝ)*base92 + (3687799/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4823/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1365_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1365_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1365_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1365_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4999/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
