-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:47:30.763006+00:00
-- url     : https://prove2.me/submissions/50d94469-32f5-4ab9-b142-a767b08ee3e7

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
theorem support_rectangle_w1041_s3_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211045141/10000000000 : ℝ)*x 0 + (544050809/1000000000 : ℝ)*x 1 + (1044319077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211045141/10000000000 : ℝ)^4117 ≤ (419240719493/3125000000000 : ℝ)^3093 := by
    have hnat : (2211045141 : ℕ)^4117*3125000000000^3093 ≤ 419240719493^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211045141 10000000000 419240719493 3125000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544050809/1000000000 : ℝ)^4117 ≤ (44475165691251/100000000000000 : ℝ)^3093 := by
    have hnat : (544050809 : ℕ)^4117*100000000000000^3093 ≤ 44475165691251^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544050809 1000000000 44475165691251 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044319077/2000000000 : ℝ)^4117 ≤ (42109131268467/100000000000000 : ℝ)^3093 := by
    have hnat : (1044319077 : ℕ)^4117*100000000000000^3093 ≤ 42109131268467^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044319077 2000000000 42109131268467 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211045141/10000000000 : ℝ), (544050809/1000000000 : ℝ), (1044319077/2000000000 : ℝ)] ![(419240719493/3125000000000 : ℝ), (44475165691251/100000000000000 : ℝ), (42109131268467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211045141/10000000000 : ℝ)|^4117 ≤ (419240719493/3125000000000 : ℝ)^3093
        have hw : |(-2211045141/10000000000 : ℝ)|=(2211045141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544050809/1000000000 : ℝ)|^4117 ≤ (44475165691251/100000000000000 : ℝ)^3093
        have hw : |(544050809/1000000000 : ℝ)|=(544050809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044319077/2000000000 : ℝ)|^4117 ≤ (42109131268467/100000000000000 : ℝ)^3093
        have hw : |(1044319077/2000000000 : ℝ)|=(1044319077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669542837/1250000000 : ℝ)*x 0 + (-2323217513/10000000000 : ℝ)*x 1 + (1044319099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669542837/1250000000 : ℝ)^4117 ≤ (4356169385631/10000000000000 : ℝ)^3093 := by
    have hnat : (669542837 : ℕ)^4117*10000000000000^3093 ≤ 4356169385631^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669542837 1250000000 4356169385631 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323217513/10000000000 : ℝ)^4117 ≤ (14329173678699/100000000000000 : ℝ)^3093 := by
    have hnat : (2323217513 : ℕ)^4117*100000000000000^3093 ≤ 14329173678699^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323217513 10000000000 14329173678699 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044319099/2000000000 : ℝ)^4117 ≤ (1052728311231/2500000000000 : ℝ)^3093 := by
    have hnat : (1044319099 : ℕ)^4117*2500000000000^3093 ≤ 1052728311231^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044319099 2000000000 1052728311231 2500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669542837/1250000000 : ℝ), (-2323217513/10000000000 : ℝ), (1044319099/2000000000 : ℝ)] ![(4356169385631/10000000000000 : ℝ), (14329173678699/100000000000000 : ℝ), (1052728311231/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669542837/1250000000 : ℝ)|^4117 ≤ (4356169385631/10000000000000 : ℝ)^3093
        have hw : |(669542837/1250000000 : ℝ)|=(669542837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2323217513/10000000000 : ℝ)|^4117 ≤ (14329173678699/100000000000000 : ℝ)^3093
        have hw : |(-2323217513/10000000000 : ℝ)|=(2323217513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044319099/2000000000 : ℝ)|^4117 ≤ (1052728311231/2500000000000 : ℝ)^3093
        have hw : |(1044319099/2000000000 : ℝ)|=(1044319099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356342711/10000000000 : ℝ)*x 0 + (1044319119/2000000000 : ℝ)*x 1 + (-1161608681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356342711/10000000000 : ℝ)^4117 ≤ (340325734521/781250000000 : ℝ)^3093 := by
    have hnat : (5356342711 : ℕ)^4117*781250000000^3093 ≤ 340325734521^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356342711 10000000000 340325734521 781250000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044319119/2000000000 : ℝ)^4117 ≤ (42109133522671/100000000000000 : ℝ)^3093 := by
    have hnat : (1044319119 : ℕ)^4117*100000000000000^3093 ≤ 42109133522671^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044319119 2000000000 42109133522671 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161608681/5000000000 : ℝ)^4117 ≤ (716458621951/5000000000000 : ℝ)^3093 := by
    have hnat : (1161608681 : ℕ)^4117*5000000000000^3093 ≤ 716458621951^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161608681 5000000000 716458621951 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356342711/10000000000 : ℝ), (1044319119/2000000000 : ℝ), (-1161608681/5000000000 : ℝ)] ![(340325734521/781250000000 : ℝ), (42109133522671/100000000000000 : ℝ), (716458621951/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356342711/10000000000 : ℝ)|^4117 ≤ (340325734521/781250000000 : ℝ)^3093
        have hw : |(5356342711/10000000000 : ℝ)|=(5356342711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044319119/2000000000 : ℝ)|^4117 ≤ (42109133522671/100000000000000 : ℝ)^3093
        have hw : |(1044319119/2000000000 : ℝ)|=(1044319119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1161608681/5000000000 : ℝ)|^4117 ≤ (716458621951/5000000000000 : ℝ)^3093
        have hw : |(-1161608681/5000000000 : ℝ)|=(1161608681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376092519/10000000000 : ℝ)*x 0 + (4167934413/10000000000 : ℝ)*x 1 + (2297421957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376092519/10000000000 : ℝ)^4117 ≤ (665718981429/2000000000000 : ℝ)^3093 := by
    have hnat : (4376092519 : ℕ)^4117*2000000000000^3093 ≤ 665718981429^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376092519 10000000000 665718981429 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167934413/10000000000 : ℝ)^4117 ≤ (1949701105237/6250000000000 : ℝ)^3093 := by
    have hnat : (4167934413 : ℕ)^4117*6250000000000^3093 ≤ 1949701105237^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167934413 10000000000 1949701105237 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2297421957/5000000000 : ℝ)^4117 ≤ (17759416616563/50000000000000 : ℝ)^3093 := by
    have hnat : (2297421957 : ℕ)^4117*50000000000000^3093 ≤ 17759416616563^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297421957 5000000000 17759416616563 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376092519/10000000000 : ℝ), (4167934413/10000000000 : ℝ), (2297421957/5000000000 : ℝ)] ![(665718981429/2000000000000 : ℝ), (1949701105237/6250000000000 : ℝ), (17759416616563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376092519/10000000000 : ℝ)|^4117 ≤ (665718981429/2000000000000 : ℝ)^3093
        have hw : |(4376092519/10000000000 : ℝ)|=(4376092519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167934413/10000000000 : ℝ)|^4117 ≤ (1949701105237/6250000000000 : ℝ)^3093
        have hw : |(4167934413/10000000000 : ℝ)|=(4167934413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2297421957/5000000000 : ℝ)|^4117 ≤ (17759416616563/50000000000000 : ℝ)^3093
        have hw : |(2297421957/5000000000 : ℝ)|=(2297421957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211069297/10000000000 : ℝ)*x 0 + (2611254979/5000000000 : ℝ)*x 1 + (5439587887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211069297/10000000000 : ℝ)^4117 ≤ (13415898117177/100000000000000 : ℝ)^3093 := by
    have hnat : (2211069297 : ℕ)^4117*100000000000000^3093 ≤ 13415898117177^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211069297 10000000000 13415898117177 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611254979/5000000000 : ℝ)^4117 ≤ (10529737215119/25000000000000 : ℝ)^3093 := by
    have hnat : (2611254979 : ℕ)^4117*25000000000000^3093 ≤ 10529737215119^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611254979 5000000000 10529737215119 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439587887/10000000000 : ℝ)^4117 ≤ (22232576503213/50000000000000 : ℝ)^3093 := by
    have hnat : (5439587887 : ℕ)^4117*50000000000000^3093 ≤ 22232576503213^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439587887 10000000000 22232576503213 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211069297/10000000000 : ℝ), (2611254979/5000000000 : ℝ), (5439587887/10000000000 : ℝ)] ![(13415898117177/100000000000000 : ℝ), (10529737215119/25000000000000 : ℝ), (22232576503213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211069297/10000000000 : ℝ)|^4117 ≤ (13415898117177/100000000000000 : ℝ)^3093
        have hw : |(-2211069297/10000000000 : ℝ)|=(2211069297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611254979/5000000000 : ℝ)|^4117 ≤ (10529737215119/25000000000000 : ℝ)^3093
        have hw : |(2611254979/5000000000 : ℝ)|=(2611254979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439587887/10000000000 : ℝ)|^4117 ≤ (22232576503213/50000000000000 : ℝ)^3093
        have hw : |(5439587887/10000000000 : ℝ)|=(5439587887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060261529/2000000000 : ℝ)*x 0 + (-1052612163/5000000000 : ℝ)*x 1 + (5439588467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060261529/2000000000 : ℝ)^4117 ≤ (42966942103081/100000000000000 : ℝ)^3093 := by
    have hnat : (1060261529 : ℕ)^4117*100000000000000^3093 ≤ 42966942103081^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060261529 2000000000 42966942103081 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052612163/5000000000 : ℝ)^4117 ≤ (6283949284753/50000000000000 : ℝ)^3093 := by
    have hnat : (1052612163 : ℕ)^4117*50000000000000^3093 ≤ 6283949284753^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052612163 5000000000 6283949284753 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439588467/10000000000 : ℝ)^4117 ≤ (22232579658601/50000000000000 : ℝ)^3093 := by
    have hnat : (5439588467 : ℕ)^4117*50000000000000^3093 ≤ 22232579658601^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439588467 10000000000 22232579658601 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060261529/2000000000 : ℝ), (-1052612163/5000000000 : ℝ), (5439588467/10000000000 : ℝ)] ![(42966942103081/100000000000000 : ℝ), (6283949284753/50000000000000 : ℝ), (22232579658601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060261529/2000000000 : ℝ)|^4117 ≤ (42966942103081/100000000000000 : ℝ)^3093
        have hw : |(1060261529/2000000000 : ℝ)|=(1060261529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052612163/5000000000 : ℝ)|^4117 ≤ (6283949284753/50000000000000 : ℝ)^3093
        have hw : |(-1052612163/5000000000 : ℝ)|=(1052612163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439588467/10000000000 : ℝ)|^4117 ≤ (22232579658601/50000000000000 : ℝ)^3093
        have hw : |(5439588467/10000000000 : ℝ)|=(5439588467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650653751/5000000000 : ℝ)*x 0 + (27197941/50000000 : ℝ)*x 1 + (-421044977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650653751/5000000000 : ℝ)^4117 ≤ (42966940560357/100000000000000 : ℝ)^3093 := by
    have hnat : (2650653751 : ℕ)^4117*100000000000000^3093 ≤ 42966940560357^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650653751 5000000000 42966940560357 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27197941/50000000 : ℝ)^4117 ≤ (44465156412069/100000000000000 : ℝ)^3093 := by
    have hnat : (27197941 : ℕ)^4117*100000000000000^3093 ≤ 44465156412069^3093*50000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27197941 50000000 44465156412069 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421044977/2000000000 : ℝ)^4117 ≤ (12567903011491/100000000000000 : ℝ)^3093 := by
    have hnat : (421044977 : ℕ)^4117*100000000000000^3093 ≤ 12567903011491^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421044977 2000000000 12567903011491 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650653751/5000000000 : ℝ), (27197941/50000000 : ℝ), (-421044977/2000000000 : ℝ)] ![(42966940560357/100000000000000 : ℝ), (44465156412069/100000000000000 : ℝ), (12567903011491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650653751/5000000000 : ℝ)|^4117 ≤ (42966940560357/100000000000000 : ℝ)^3093
        have hw : |(2650653751/5000000000 : ℝ)|=(2650653751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27197941/50000000 : ℝ)|^4117 ≤ (44465156412069/100000000000000 : ℝ)^3093
        have hw : |(27197941/50000000 : ℝ)|=(27197941/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421044977/2000000000 : ℝ)|^4117 ≤ (12567903011491/100000000000000 : ℝ)^3093
        have hw : |(-421044977/2000000000 : ℝ)|=(421044977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s3_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875227809/2000000000 : ℝ)*x 0 + (4593061663/10000000000 : ℝ)*x 1 + (1042431903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875227809/2000000000 : ℝ)^4117 ≤ (33286420126731/100000000000000 : ℝ)^3093 := by
    have hnat : (875227809 : ℕ)^4117*100000000000000^3093 ≤ 33286420126731^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875227809 2000000000 33286420126731 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4593061663/10000000000 : ℝ)^4117 ≤ (35500496166893/100000000000000 : ℝ)^3093 := by
    have hnat : (4593061663 : ℕ)^4117*100000000000000^3093 ≤ 35500496166893^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593061663 10000000000 35500496166893 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042431903/2500000000 : ℝ)^4117 ≤ (1560654184551/5000000000000 : ℝ)^3093 := by
    have hnat : (1042431903 : ℕ)^4117*5000000000000^3093 ≤ 1560654184551^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042431903 2500000000 1560654184551 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875227809/2000000000 : ℝ), (4593061663/10000000000 : ℝ), (1042431903/2500000000 : ℝ)] ![(33286420126731/100000000000000 : ℝ), (35500496166893/100000000000000 : ℝ), (1560654184551/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875227809/2000000000 : ℝ)|^4117 ≤ (33286420126731/100000000000000 : ℝ)^3093
        have hw : |(875227809/2000000000 : ℝ)|=(875227809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4593061663/10000000000 : ℝ)|^4117 ≤ (35500496166893/100000000000000 : ℝ)^3093
        have hw : |(4593061663/10000000000 : ℝ)|=(4593061663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042431903/2500000000 : ℝ)|^4117 ≤ (1560654184551/5000000000000 : ℝ)^3093
        have hw : |(1042431903/2500000000 : ℝ)|=(1042431903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1289/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14943/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2103/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2147/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2103/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2147/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2103/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2147/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2103/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2147/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2103/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2147/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2103/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2147/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2147/25000 : ℝ) ^ (8233/2048 : ℝ) ≤ (517875256430269/10000000000000000000 : ℝ) := by
    have hpowers : (2147/25000 : ℝ)^8233 ≤ (517875256430269/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2147 : ℕ)^8233*10000000000000000000^2048 ≤ 517875256430269^2048*25000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2147 25000 517875256430269 10000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2147/25000 : ℝ)) (X := (517875256430269/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2103/12500 : ℝ) ^ (8233/2048 : ℝ) ≤ (1932682499002467/2500000000000000000 : ℝ) := by
    have hpowers : (2103/12500 : ℝ)^8233 ≤ (1932682499002467/2500000000000000000 : ℝ)^2048 := by
      have hnat : (2103 : ℕ)^8233*2500000000000000000^2048 ≤ 1932682499002467^2048*12500^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2103 12500 1932682499002467 2500000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2103/12500 : ℝ)) (X := (1932682499002467/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000517875256430269/5000000000000000000 : ℝ) ≤ (2000051527621259/2000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (5000517875256430269/5000000000000000000 : ℝ)^2048 ≤ (2000051527621259/2000000000000000 : ℝ)^8233 := by
      have hnat : (5000517875256430269 : ℕ)^2048*2000000000000000^8233 ≤ 2000051527621259^8233*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000517875256430269 5000000000000000000 2000051527621259 2000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051527621259/2000000000000000 : ℝ)) (X := (5000517875256430269/5000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10008248605252440137/10000000000000000000 : ℝ) ≤ (10002051246443457/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (10008248605252440137/10000000000000000000 : ℝ)^2048 ≤ (10002051246443457/10000000000000000 : ℝ)^8233 := by
      have hnat : (10008248605252440137 : ℕ)^2048*10000000000000000^8233 ≤ 10002051246443457^8233*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008248605252440137 10000000000000000000 10002051246443457 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002051246443457/10000000000000000 : ℝ)) (X := (10008248605252440137/10000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251932682499002467/1250000000000000000 : ℝ) ≤ (10003844854780619/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (1251932682499002467/1250000000000000000 : ℝ)^2048 ≤ (10003844854780619/10000000000000000 : ℝ)^8233 := by
      have hnat : (1251932682499002467 : ℕ)^2048*10000000000000000^8233 ≤ 10003844854780619^8233*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251932682499002467 1250000000000000000 10003844854780619 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003844854780619/10000000000000000 : ℝ)) (X := (1251932682499002467/1250000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(517875256430269/10000000000000000000 : ℝ) ≤ ((20582828722661087777/20590000000000000000 : ℝ)+2*(896804168581/411800000000000 : ℝ)*(2147/25000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (20582828722661087777/20590000000000000000 : ℝ)+2*(896804168581/411800000000000 : ℝ)*(2147/25000 : ℝ)=(2000051527621259/2000000000000000 : ℝ) by norm_num, show 1+2*(517875256430269/10000000000000000000 : ℝ)=(5000517875256430269/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1932682499002467/2500000000000000000 : ℝ)+(517875256430269/10000000000000000000 : ℝ) ≤ ((20582828722661087777/20590000000000000000 : ℝ)+(896804168581/411800000000000 : ℝ)*((2103/12500 : ℝ)+(2147/25000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (20582828722661087777/20590000000000000000 : ℝ)+(896804168581/411800000000000 : ℝ)*((2103/12500 : ℝ)+(2147/25000 : ℝ))=(10002051246443457/10000000000000000 : ℝ) by norm_num, show 1+(1932682499002467/2500000000000000000 : ℝ)+(517875256430269/10000000000000000000 : ℝ)=(10008248605252440137/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1932682499002467/2500000000000000000 : ℝ) ≤ ((20582828722661087777/20590000000000000000 : ℝ)+2*(896804168581/411800000000000 : ℝ)*(2103/12500 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (20582828722661087777/20590000000000000000 : ℝ)+2*(896804168581/411800000000000 : ℝ)*(2103/12500 : ℝ)=(10003844854780619/10000000000000000 : ℝ) by norm_num, show 1+2*(1932682499002467/2500000000000000000 : ℝ)=(1251932682499002467/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20582828722661087777/20590000000000000000 : ℝ)*(X 1 0+X 2 0)+(896804168581/411800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2147/25000 : ℝ)) (hi := (2103/12500 : ℝ)) (c := (20582828722661087777/20590000000000000000 : ℝ)) (alpha := (896804168581/411800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20582828722661087777/20590000000000000000 : ℝ)*(X 0 1+X 2 1)+(896804168581/411800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2147/25000 : ℝ)) (hi := (2103/12500 : ℝ)) (c := (20582828722661087777/20590000000000000000 : ℝ)) (alpha := (896804168581/411800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20582828722661087777/20590000000000000000 : ℝ)*(X 0 2+X 1 2)+(896804168581/411800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (2147/25000 : ℝ)) (hi := (2103/12500 : ℝ)) (c := (20582828722661087777/20590000000000000000 : ℝ)) (alpha := (896804168581/411800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2211045141/10000000000 : ℝ)*X 0 0+(544050809/1000000000 : ℝ)*X 0 1+(1044319077/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669542837/1250000000 : ℝ)*X 1 0+(-2323217513/10000000000 : ℝ)*X 1 1+(1044319099/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356342711/10000000000 : ℝ)*X 2 0+(1044319119/2000000000 : ℝ)*X 2 1+(-1161608681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376092519/10000000000 : ℝ)*X 0 0+(4167934413/10000000000 : ℝ)*X 0 1+(2297421957/5000000000 : ℝ)*X 0 2+(4376092519/10000000000 : ℝ)*X 1 0+(4167934413/10000000000 : ℝ)*X 1 1+(2297421957/5000000000 : ℝ)*X 1 2+(4376092519/10000000000 : ℝ)*X 2 0+(4167934413/10000000000 : ℝ)*X 2 1+(2297421957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2211069297/10000000000 : ℝ)*X 0 0+(2611254979/5000000000 : ℝ)*X 0 1+(5439587887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060261529/2000000000 : ℝ)*X 1 0+(-1052612163/5000000000 : ℝ)*X 1 1+(5439588467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650653751/5000000000 : ℝ)*X 2 0+(27197941/50000000 : ℝ)*X 2 1+(-421044977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875227809/2000000000 : ℝ)*X 0 0+(4593061663/10000000000 : ℝ)*X 0 1+(1042431903/2500000000 : ℝ)*X 0 2+(875227809/2000000000 : ℝ)*X 1 0+(4593061663/10000000000 : ℝ)*X 1 1+(1042431903/2500000000 : ℝ)*X 1 2+(875227809/2000000000 : ℝ)*X 2 0+(4593061663/10000000000 : ℝ)*X 2 1+(1042431903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1727942437613747205270643281/1029500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (592095573/100000000000000 : ℝ)*(base19) + (113384823/25000000000000 : ℝ)*(base23) + (81067577/100000000000000 : ℝ)*(lower2) + (25545717/100000000000000 : ℝ)*(upper3) + (53465869/100000000000000 : ℝ)*(upper5) + (3455241634751451/100000000000000 : ℝ)*(major0) + (3455241634751451/100000000000000 : ℝ)*(major1) + (3455241634751451/100000000000000 : ℝ)*(major2) + (1142010669185441/25000000000000 : ℝ)*(sp0) + (571007024575639/12500000000000 : ℝ)*(sp1) + (4568056335161393/100000000000000 : ℝ)*(sp2) + (1171210751460383/50000000000000 : ℝ)*(sp3) + (352798973/2500000000000 : ℝ)*(sp4) + (4921933817/100000000000000 : ℝ)*(sp7) + (1171213212427291/50000000000000 : ℝ)*(f.failure) + (1142014197175171/25000000000000 : ℝ)*(f.sum) + (2715306311581/20590000000000000000000000000 : ℝ)*base65 + (57666370687919463/71000000000000000000000000000000 : ℝ)*base67 + (669491500601080537/71000000000000000000000000000000 : ℝ)*base70 + (173305299974080537/71000000000000000000000000000000 : ℝ)*base72 + (23748304527039/20590000000000000000000000000 : ℝ)*base74 + (832820558061080537/71000000000000000000000000000000 : ℝ)*base76 + (84320607415080537/71000000000000000000000000000000 : ℝ)*base78 + (424518562922919463/71000000000000000000000000000000 : ℝ)*base79 + (40325648917549/20590000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (253057/39062500000000000000 : ℝ)*base90 + (253057/39062500000000000000 : ℝ)*base92 + (253057/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3157552044869515034904783471/514750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (828992817/50000000000000 : ℝ)*(base19) + (190176027/12500000000000 : ℝ)*(base23) + (2860373/12500000000000 : ℝ)*(upper2) + (2276673/781250000000 : ℝ)*(upper3) + (1742209235869941/50000000000000 : ℝ)*(major0) + (1742209235869941/50000000000000 : ℝ)*(major1) + (1742209235869941/50000000000000 : ℝ)*(major2) + (33573563849/100000000000000 : ℝ)*(sp1) + (1411461867/5000000000000 : ℝ)*(sp2) + (1397352629/100000000000000 : ℝ)*(sp3) + (575828792365223/12500000000000 : ℝ)*(sp4) + (4606595107372301/100000000000000 : ℝ)*(sp5) + (4606600588276227/100000000000000 : ℝ)*(sp6) + (1181102501366893/50000000000000 : ℝ)*(sp7) + (1181103200043207/50000000000000 : ℝ)*(f.failure) + (575828792365223/12500000000000 : ℝ)*(f.sum) + (49496770521657/5147500000000000000000000000 : ℝ)*base66 + (271827525978746167/35500000000000000000000000000000 : ℝ)*base68 + (48510757566753833/35500000000000000000000000000000 : ℝ)*base69 + (247261593535246167/35500000000000000000000000000000 : ℝ)*base72 + (59996032234719/10295000000000000000000000000 : ℝ)*base74 + (71895231869753833/35500000000000000000000000000000 : ℝ)*base75 + (325647213932746167/35500000000000000000000000000000 : ℝ)*base78 + (114211559772746167/35500000000000000000000000000000 : ℝ)*base80 + (2255745695091/2573750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31767/4882812500000000000 : ℝ)*base89 + (31767/4882812500000000000 : ℝ)*base91 + (31767/4882812500000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1041_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1289/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s4_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-221497351/1000000000 : ℝ)*x 0 + (5407230957/10000000000 : ℝ)*x 1 + (1313076869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221497351/1000000000 : ℝ)^4117 ≤ (6723719677073/50000000000000 : ℝ)^3093 := by
    have hnat : (221497351 : ℕ)^4117*50000000000000^3093 ≤ 6723719677073^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221497351 1000000000 6723719677073 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407230957/10000000000 : ℝ)^4117 ≤ (44113435786101/100000000000000 : ℝ)^3093 := by
    have hnat : (5407230957 : ℕ)^4117*100000000000000^3093 ≤ 44113435786101^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407230957 10000000000 44113435786101 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313076869/2500000000 : ℝ)^4117 ≤ (42439124843949/100000000000000 : ℝ)^3093 := by
    have hnat : (1313076869 : ℕ)^4117*100000000000000^3093 ≤ 42439124843949^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313076869 2500000000 42439124843949 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221497351/1000000000 : ℝ), (5407230957/10000000000 : ℝ), (1313076869/2500000000 : ℝ)] ![(6723719677073/50000000000000 : ℝ), (44113435786101/100000000000000 : ℝ), (42439124843949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221497351/1000000000 : ℝ)|^4117 ≤ (6723719677073/50000000000000 : ℝ)^3093
        have hw : |(-221497351/1000000000 : ℝ)|=(221497351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407230957/10000000000 : ℝ)|^4117 ≤ (44113435786101/100000000000000 : ℝ)^3093
        have hw : |(5407230957/10000000000 : ℝ)|=(5407230957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313076869/2500000000 : ℝ)|^4117 ≤ (42439124843949/100000000000000 : ℝ)^3093
        have hw : |(1313076869/2500000000 : ℝ)|=(1313076869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674061407/5000000000 : ℝ)*x 0 + (-2293796443/10000000000 : ℝ)*x 1 + (2100923/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674061407/5000000000 : ℝ)^4117 ≤ (21736367155213/50000000000000 : ℝ)^3093 := by
    have hnat : (2674061407 : ℕ)^4117*50000000000000^3093 ≤ 21736367155213^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674061407 5000000000 21736367155213 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2293796443/10000000000 : ℝ)^4117 ≤ (14088140562191/100000000000000 : ℝ)^3093 := by
    have hnat : (2293796443 : ℕ)^4117*100000000000000^3093 ≤ 14088140562191^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293796443 10000000000 14088140562191 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100923/4000000 : ℝ)^4117 ≤ (42439125102073/100000000000000 : ℝ)^3093 := by
    have hnat : (2100923 : ℕ)^4117*100000000000000^3093 ≤ 42439125102073^3093*4000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100923 4000000 42439125102073 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674061407/5000000000 : ℝ), (-2293796443/10000000000 : ℝ), (2100923/4000000 : ℝ)] ![(21736367155213/50000000000000 : ℝ), (14088140562191/100000000000000 : ℝ), (42439125102073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674061407/5000000000 : ℝ)|^4117 ≤ (21736367155213/50000000000000 : ℝ)^3093
        have hw : |(2674061407/5000000000 : ℝ)|=(2674061407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2293796443/10000000000 : ℝ)|^4117 ≤ (14088140562191/100000000000000 : ℝ)^3093
        have hw : |(-2293796443/10000000000 : ℝ)|=(2293796443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2100923/4000000 : ℝ)|^4117 ≤ (42439125102073/100000000000000 : ℝ)^3093
        have hw : |(2100923/4000000 : ℝ)|=(2100923/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069624573/2000000000 : ℝ)*x 0 + (5252307423/10000000000 : ℝ)*x 1 + (-1146898239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069624573/2000000000 : ℝ)^4117 ≤ (5434091857779/12500000000000 : ℝ)^3093 := by
    have hnat : (1069624573 : ℕ)^4117*12500000000000^3093 ≤ 5434091857779^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069624573 2000000000 5434091857779 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252307423/10000000000 : ℝ)^4117 ≤ (1697564970957/4000000000000 : ℝ)^3093 := by
    have hnat : (5252307423 : ℕ)^4117*4000000000000^3093 ≤ 1697564970957^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252307423 10000000000 1697564970957 4000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146898239/5000000000 : ℝ)^4117 ≤ (3522035212081/25000000000000 : ℝ)^3093 := by
    have hnat : (1146898239 : ℕ)^4117*25000000000000^3093 ≤ 3522035212081^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146898239 5000000000 3522035212081 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069624573/2000000000 : ℝ), (5252307423/10000000000 : ℝ), (-1146898239/5000000000 : ℝ)] ![(5434091857779/12500000000000 : ℝ), (1697564970957/4000000000000 : ℝ), (3522035212081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069624573/2000000000 : ℝ)|^4117 ≤ (5434091857779/12500000000000 : ℝ)^3093
        have hw : |(1069624573/2000000000 : ℝ)|=(1069624573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252307423/10000000000 : ℝ)|^4117 ≤ (1697564970957/4000000000000 : ℝ)^3093
        have hw : |(5252307423/10000000000 : ℝ)|=(5252307423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1146898239/5000000000 : ℝ)|^4117 ≤ (3522035212081/25000000000000 : ℝ)^3093
        have hw : |(-1146898239/5000000000 : ℝ)|=(1146898239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547303397/1250000000 : ℝ)*x 0 + (4230020547/10000000000 : ℝ)*x 1 + (4532142893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547303397/1250000000 : ℝ)^4117 ≤ (416369856151/1250000000000 : ℝ)^3093 := by
    have hnat : (547303397 : ℕ)^4117*1250000000000^3093 ≤ 416369856151^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547303397 1250000000 416369856151 1250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230020547/10000000000 : ℝ)^4117 ≤ (31815270611737/100000000000000 : ℝ)^3093 := by
    have hnat : (4230020547 : ℕ)^4117*100000000000000^3093 ≤ 31815270611737^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230020547 10000000000 31815270611737 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532142893/10000000000 : ℝ)^4117 ≤ (17437570441057/50000000000000 : ℝ)^3093 := by
    have hnat : (4532142893 : ℕ)^4117*50000000000000^3093 ≤ 17437570441057^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532142893 10000000000 17437570441057 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547303397/1250000000 : ℝ), (4230020547/10000000000 : ℝ), (4532142893/10000000000 : ℝ)] ![(416369856151/1250000000000 : ℝ), (31815270611737/100000000000000 : ℝ), (17437570441057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547303397/1250000000 : ℝ)|^4117 ≤ (416369856151/1250000000000 : ℝ)^3093
        have hw : |(547303397/1250000000 : ℝ)|=(547303397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230020547/10000000000 : ℝ)|^4117 ≤ (31815270611737/100000000000000 : ℝ)^3093
        have hw : |(4230020547/10000000000 : ℝ)|=(4230020547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532142893/10000000000 : ℝ)|^4117 ≤ (17437570441057/50000000000000 : ℝ)^3093
        have hw : |(4532142893/10000000000 : ℝ)|=(4532142893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-110749111/500000000 : ℝ)*x 0 + (5252765959/10000000000 : ℝ)*x 1 + (5406770371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110749111/500000000 : ℝ)^4117 ≤ (672375487041/5000000000000 : ℝ)^3093 := by
    have hnat : (110749111 : ℕ)^4117*5000000000000^3093 ≤ 672375487041^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110749111 500000000 672375487041 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252765959/10000000000 : ℝ)^4117 ≤ (21222027988591/50000000000000 : ℝ)^3093 := by
    have hnat : (5252765959 : ℕ)^4117*50000000000000^3093 ≤ 21222027988591^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252765959 10000000000 21222027988591 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406770371/10000000000 : ℝ)^4117 ≤ (8821686854347/20000000000000 : ℝ)^3093 := by
    have hnat : (5406770371 : ℕ)^4117*20000000000000^3093 ≤ 8821686854347^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406770371 10000000000 8821686854347 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110749111/500000000 : ℝ), (5252765959/10000000000 : ℝ), (5406770371/10000000000 : ℝ)] ![(672375487041/5000000000000 : ℝ), (21222027988591/50000000000000 : ℝ), (8821686854347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110749111/500000000 : ℝ)|^4117 ≤ (672375487041/5000000000000 : ℝ)^3093
        have hw : |(-110749111/500000000 : ℝ)|=(110749111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252765959/10000000000 : ℝ)|^4117 ≤ (21222027988591/50000000000000 : ℝ)^3093
        have hw : |(5252765959/10000000000 : ℝ)|=(5252765959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406770371/10000000000 : ℝ)|^4117 ≤ (8821686854347/20000000000000 : ℝ)^3093
        have hw : |(5406770371/10000000000 : ℝ)|=(5406770371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2654590387/5000000000 : ℝ)*x 0 + (-2139333633/10000000000 : ℝ)*x 1 + (1351692577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654590387/5000000000 : ℝ)^4117 ≤ (43051900531879/100000000000000 : ℝ)^3093 := by
    have hnat : (2654590387 : ℕ)^4117*100000000000000^3093 ≤ 43051900531879^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654590387 5000000000 43051900531879 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139333633/10000000000 : ℝ)^4117 ≤ (6419832933489/50000000000000 : ℝ)^3093 := by
    have hnat : (2139333633 : ℕ)^4117*50000000000000^3093 ≤ 6419832933489^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139333633 10000000000 6419832933489 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351692577/2500000000 : ℝ)^4117 ≤ (22054216793813/50000000000000 : ℝ)^3093 := by
    have hnat : (1351692577 : ℕ)^4117*50000000000000^3093 ≤ 22054216793813^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351692577 2500000000 22054216793813 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654590387/5000000000 : ℝ), (-2139333633/10000000000 : ℝ), (1351692577/2500000000 : ℝ)] ![(43051900531879/100000000000000 : ℝ), (6419832933489/50000000000000 : ℝ), (22054216793813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654590387/5000000000 : ℝ)|^4117 ≤ (43051900531879/100000000000000 : ℝ)^3093
        have hw : |(2654590387/5000000000 : ℝ)|=(2654590387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139333633/10000000000 : ℝ)|^4117 ≤ (6419832933489/50000000000000 : ℝ)^3093
        have hw : |(-2139333633/10000000000 : ℝ)|=(2139333633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351692577/2500000000 : ℝ)|^4117 ≤ (22054216793813/50000000000000 : ℝ)^3093
        have hw : |(1351692577/2500000000 : ℝ)|=(1351692577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309180727/10000000000 : ℝ)*x 0 + (5406770339/10000000000 : ℝ)*x 1 + (-1069666827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309180727/10000000000 : ℝ)^4117 ≤ (43051900024581/100000000000000 : ℝ)^3093 := by
    have hnat : (5309180727 : ℕ)^4117*100000000000000^3093 ≤ 43051900024581^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309180727 10000000000 43051900024581 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406770339/10000000000 : ℝ)^4117 ≤ (44108433924251/100000000000000 : ℝ)^3093 := by
    have hnat : (5406770339 : ℕ)^4117*100000000000000^3093 ≤ 44108433924251^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406770339 10000000000 44108433924251 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069666827/5000000000 : ℝ)^4117 ≤ (12839666034741/100000000000000 : ℝ)^3093 := by
    have hnat : (1069666827 : ℕ)^4117*100000000000000^3093 ≤ 12839666034741^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069666827 5000000000 12839666034741 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309180727/10000000000 : ℝ), (5406770339/10000000000 : ℝ), (-1069666827/5000000000 : ℝ)] ![(43051900024581/100000000000000 : ℝ), (44108433924251/100000000000000 : ℝ), (12839666034741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309180727/10000000000 : ℝ)|^4117 ≤ (43051900024581/100000000000000 : ℝ)^3093
        have hw : |(5309180727/10000000000 : ℝ)|=(5309180727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406770339/10000000000 : ℝ)|^4117 ≤ (44108433924251/100000000000000 : ℝ)^3093
        have hw : |(5406770339/10000000000 : ℝ)|=(5406770339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069666827/5000000000 : ℝ)|^4117 ≤ (12839666034741/100000000000000 : ℝ)^3093
        have hw : |(-1069666827/5000000000 : ℝ)|=(1069666827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s4_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4378443739/10000000000 : ℝ)*x 0 + (2265624029/5000000000 : ℝ)*x 1 + (105772981/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378443739/10000000000 : ℝ)^4117 ≤ (520464940853/1562500000000 : ℝ)^3093 := by
    have hnat : (4378443739 : ℕ)^4117*1562500000000^3093 ≤ 520464940853^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378443739 10000000000 520464940853 1562500000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265624029/5000000000 : ℝ)^4117 ≤ (8716493919767/25000000000000 : ℝ)^3093 := by
    have hnat : (2265624029 : ℕ)^4117*25000000000000^3093 ≤ 8716493919767^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265624029 5000000000 8716493919767 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105772981/250000000 : ℝ)^4117 ≤ (31824268088283/100000000000000 : ℝ)^3093 := by
    have hnat : (105772981 : ℕ)^4117*100000000000000^3093 ≤ 31824268088283^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105772981 250000000 31824268088283 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378443739/10000000000 : ℝ), (2265624029/5000000000 : ℝ), (105772981/250000000 : ℝ)] ![(520464940853/1562500000000 : ℝ), (8716493919767/25000000000000 : ℝ), (31824268088283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378443739/10000000000 : ℝ)|^4117 ≤ (520464940853/1562500000000 : ℝ)^3093
        have hw : |(4378443739/10000000000 : ℝ)|=(4378443739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265624029/5000000000 : ℝ)|^4117 ≤ (8716493919767/25000000000000 : ℝ)^3093
        have hw : |(2265624029/5000000000 : ℝ)|=(2265624029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105772981/250000000 : ℝ)|^4117 ≤ (31824268088283/100000000000000 : ℝ)^3093
        have hw : |(105772981/250000000 : ℝ)|=(105772981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1289/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1371/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1289/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1289/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1289/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1289/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1289/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1289/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1289/12500 : ℝ) ^ (8233/2048 : ℝ) ≤ (10804861512083141/100000000000000000000 : ℝ) := by
    have hpowers : (1289/12500 : ℝ)^8233 ≤ (10804861512083141/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1289 : ℕ)^8233*100000000000000000000^2048 ≤ 10804861512083141^2048*12500^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1289 12500 10804861512083141 100000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1289/12500 : ℝ)) (X := (10804861512083141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14943/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (23999037360048437/50000000000000000000 : ℝ) := by
    have hpowers : (14943/100000 : ℝ)^8233 ≤ (23999037360048437/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14943 : ℕ)^8233*50000000000000000000^2048 ≤ 23999037360048437^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14943 100000 23999037360048437 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14943/100000 : ℝ)) (X := (23999037360048437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010804861512083141/50000000000000000000 : ℝ) ≤ (10000537509059223/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50010804861512083141/50000000000000000000 : ℝ)^2048 ≤ (10000537509059223/10000000000000000 : ℝ)^8233 := by
      have hnat : (50010804861512083141 : ℕ)^2048*10000000000000000^8233 ≤ 10000537509059223^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010804861512083141 50000000000000000000 10000537509059223 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537509059223/10000000000000000 : ℝ)) (X := (50010804861512083141/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011760587246436003/20000000000000000000 : ℝ) ≤ (10001462429523347/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (20011760587246436003/20000000000000000000 : ℝ)^2048 ≤ (10001462429523347/10000000000000000 : ℝ)^8233 := by
      have hnat : (20011760587246436003 : ℕ)^2048*10000000000000000^8233 ≤ 10001462429523347^8233*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011760587246436003 20000000000000000000 10001462429523347 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001462429523347/10000000000000000 : ℝ)) (X := (20011760587246436003/20000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25023999037360048437/25000000000000000000 : ℝ) ≤ (10002387349987471/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (25023999037360048437/25000000000000000000 : ℝ)^2048 ≤ (10002387349987471/10000000000000000 : ℝ)^8233 := by
      have hnat : (25023999037360048437 : ℕ)^2048*10000000000000000^8233 ≤ 10002387349987471^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023999037360048437 25000000000000000000 10002387349987471 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002387349987471/10000000000000000 : ℝ)) (X := (25023999037360048437/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10804861512083141/100000000000000000000 : ℝ) ≤ ((46293413644801168337/46310000000000000000 : ℝ)+2*(231230116031/115775000000000 : ℝ)*(1289/12500 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (46293413644801168337/46310000000000000000 : ℝ)+2*(231230116031/115775000000000 : ℝ)*(1289/12500 : ℝ)=(10000537509059223/10000000000000000 : ℝ) by norm_num, show 1+2*(10804861512083141/100000000000000000000 : ℝ)=(50010804861512083141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23999037360048437/50000000000000000000 : ℝ)+(10804861512083141/100000000000000000000 : ℝ) ≤ ((46293413644801168337/46310000000000000000 : ℝ)+(231230116031/115775000000000 : ℝ)*((14943/100000 : ℝ)+(1289/12500 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (46293413644801168337/46310000000000000000 : ℝ)+(231230116031/115775000000000 : ℝ)*((14943/100000 : ℝ)+(1289/12500 : ℝ))=(10001462429523347/10000000000000000 : ℝ) by norm_num, show 1+(23999037360048437/50000000000000000000 : ℝ)+(10804861512083141/100000000000000000000 : ℝ)=(20011760587246436003/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23999037360048437/50000000000000000000 : ℝ) ≤ ((46293413644801168337/46310000000000000000 : ℝ)+2*(231230116031/115775000000000 : ℝ)*(14943/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (46293413644801168337/46310000000000000000 : ℝ)+2*(231230116031/115775000000000 : ℝ)*(14943/100000 : ℝ)=(10002387349987471/10000000000000000 : ℝ) by norm_num, show 1+2*(23999037360048437/50000000000000000000 : ℝ)=(25023999037360048437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46293413644801168337/46310000000000000000 : ℝ)*(X 1 0+X 2 0)+(231230116031/115775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1289/12500 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (46293413644801168337/46310000000000000000 : ℝ)) (alpha := (231230116031/115775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46293413644801168337/46310000000000000000 : ℝ)*(X 0 1+X 2 1)+(231230116031/115775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1289/12500 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (46293413644801168337/46310000000000000000 : ℝ)) (alpha := (231230116031/115775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46293413644801168337/46310000000000000000 : ℝ)*(X 0 2+X 1 2)+(231230116031/115775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1289/12500 : ℝ)) (hi := (14943/100000 : ℝ)) (c := (46293413644801168337/46310000000000000000 : ℝ)) (alpha := (231230116031/115775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-221497351/1000000000 : ℝ)*X 0 0+(5407230957/10000000000 : ℝ)*X 0 1+(1313076869/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674061407/5000000000 : ℝ)*X 1 0+(-2293796443/10000000000 : ℝ)*X 1 1+(2100923/4000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069624573/2000000000 : ℝ)*X 2 0+(5252307423/10000000000 : ℝ)*X 2 1+(-1146898239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547303397/1250000000 : ℝ)*X 0 0+(4230020547/10000000000 : ℝ)*X 0 1+(4532142893/10000000000 : ℝ)*X 0 2+(547303397/1250000000 : ℝ)*X 1 0+(4230020547/10000000000 : ℝ)*X 1 1+(4532142893/10000000000 : ℝ)*X 1 2+(547303397/1250000000 : ℝ)*X 2 0+(4230020547/10000000000 : ℝ)*X 2 1+(4532142893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110749111/500000000 : ℝ)*X 0 0+(5252765959/10000000000 : ℝ)*X 0 1+(5406770371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654590387/5000000000 : ℝ)*X 1 0+(-2139333633/10000000000 : ℝ)*X 1 1+(1351692577/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309180727/10000000000 : ℝ)*X 2 0+(5406770339/10000000000 : ℝ)*X 2 1+(-1069666827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378443739/10000000000 : ℝ)*X 0 0+(2265624029/5000000000 : ℝ)*X 0 1+(105772981/250000000 : ℝ)*X 0 2+(4378443739/10000000000 : ℝ)*X 1 0+(2265624029/5000000000 : ℝ)*X 1 1+(105772981/250000000 : ℝ)*X 1 2+(4378443739/10000000000 : ℝ)*X 2 0+(2265624029/5000000000 : ℝ)*X 2 1+(105772981/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2103806934966958515659261649/1157750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55593491/12500000000000 : ℝ)*(base19) + (500517311/100000000000000 : ℝ)*(base23) + (74746357/100000000000000 : ℝ)*(upper3) + (309343/10000000000000 : ℝ)*(upper4) + (9116013/25000000000000 : ℝ)*(upper5) + (4882374253756059/100000000000000 : ℝ)*(major0) + (4882374253756059/100000000000000 : ℝ)*(major1) + (4882374253756059/100000000000000 : ℝ)*(major2) + (6454810197865613/100000000000000 : ℝ)*(sp0) + (322740979352779/5000000000000 : ℝ)*(sp1) + (3227409765643099/50000000000000 : ℝ)*(sp2) + (1654961200933713/50000000000000 : ℝ)*(sp3) + (1966787579/20000000000000 : ℝ)*(sp4) + (751658683/12500000000000 : ℝ)*(sp7) + (330992841513689/10000000000000 : ℝ)*(f.failure) + (6454820031803509/100000000000000 : ℝ)*(f.sum) + (32701446614153/11577500000000000000000000000 : ℝ)*base65 + (2896841828068699647/421000000000000000000000000000000 : ℝ)*base68 + (3160312776819699647/421000000000000000000000000000000 : ℝ)*base70 + (632348551220699647/421000000000000000000000000000000 : ℝ)*base72 + (26805203555623/11577500000000000000000000000 : ℝ)*base73 + (1647877925126699647/421000000000000000000000000000000 : ℝ)*base76 + (2778292370629300353/421000000000000000000000000000000 : ℝ)*base77 + (8276106097236699647/421000000000000000000000000000000 : ℝ)*base80 + (60609310937727/11577500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (66847/7812500000000000000 : ℝ)*base89 + (66847/7812500000000000000 : ℝ)*base91 + (66847/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105982244106854247341743893/14471875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1713734127/100000000000000 : ℝ)*(base19) + (89509657/5000000000000 : ℝ)*(base23) + (103288331/100000000000000 : ℝ)*(upper2) + (26027599/50000000000000 : ℝ)*(upper3) + (201081059/50000000000000 : ℝ)*(upper5) + (30696900155931/625000000000 : ℝ)*(major0) + (30696900155931/625000000000 : ℝ)*(major1) + (30696900155931/625000000000 : ℝ)*(major2) + (44942486223/100000000000000 : ℝ)*(sp1) + (36679803997/100000000000000 : ℝ)*(sp2) + (1623332830732533/25000000000000 : ℝ)*(sp4) + (3246642333354891/50000000000000 : ℝ)*(sp5) + (3246646426466497/50000000000000 : ℝ)*(sp6) + (1664838241428471/50000000000000 : ℝ)*(sp7) + (1664838241428471/50000000000000 : ℝ)*(f.failure) + (1623332830732533/25000000000000 : ℝ)*(f.sum) + (1862317035463/463100000000000000000000000 : ℝ)*base66 + (19269791496336977/2631250000000000000000000000000 : ℝ)*base67 + (27429066648911977/2631250000000000000000000000000 : ℝ)*base69 + (10258395187313023/2631250000000000000000000000000 : ℝ)*base72 + (23507895162537/4631000000000000000000000000 : ℝ)*base73 + (20904602351011977/2631250000000000000000000000000 : ℝ)*base75 + (22100256178230727/2631250000000000000000000000000 : ℝ)*base77 + (31802808597030727/2631250000000000000000000000000 : ℝ)*base79 + (2997950650283/463100000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (188271/19531250000000000000 : ℝ)*base90 + (188271/19531250000000000000 : ℝ)*base92 + (188271/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1041_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1289/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s5_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107938427/5000000000 : ℝ)*x 0 + (5397727091/10000000000 : ℝ)*x 1 + (5261219161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107938427/5000000000 : ℝ)^4117 ≤ (2690947977149/20000000000000 : ℝ)^3093 := by
    have hnat : (1107938427 : ℕ)^4117*20000000000000^3093 ≤ 2690947977149^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107938427 5000000000 2690947977149 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397727091/10000000000 : ℝ)^4117 ≤ (4401026166199/10000000000000 : ℝ)^3093 := by
    have hnat : (5397727091 : ℕ)^4117*10000000000000^3093 ≤ 4401026166199^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397727091 10000000000 4401026166199 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261219161/10000000000 : ℝ)^4117 ≤ (42534998428879/100000000000000 : ℝ)^3093 := by
    have hnat : (5261219161 : ℕ)^4117*100000000000000^3093 ≤ 42534998428879^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261219161 10000000000 42534998428879 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107938427/5000000000 : ℝ), (5397727091/10000000000 : ℝ), (5261219161/10000000000 : ℝ)] ![(2690947977149/20000000000000 : ℝ), (4401026166199/10000000000000 : ℝ), (42534998428879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107938427/5000000000 : ℝ)|^4117 ≤ (2690947977149/20000000000000 : ℝ)^3093
        have hw : |(-1107938427/5000000000 : ℝ)|=(1107938427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397727091/10000000000 : ℝ)|^4117 ≤ (4401026166199/10000000000000 : ℝ)^3093
        have hw : |(5397727091/10000000000 : ℝ)|=(5397727091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261219161/10000000000 : ℝ)|^4117 ≤ (42534998428879/100000000000000 : ℝ)^3093
        have hw : |(5261219161/10000000000 : ℝ)|=(5261219161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345762171/10000000000 : ℝ)*x 0 + (-2285187931/10000000000 : ℝ)*x 1 + (5261219079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345762171/10000000000 : ℝ)^4117 ≤ (135772483283/312500000000 : ℝ)^3093 := by
    have hnat : (5345762171 : ℕ)^4117*312500000000^3093 ≤ 135772483283^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345762171 10000000000 135772483283 312500000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285187931/10000000000 : ℝ)^4117 ≤ (7008903895963/50000000000000 : ℝ)^3093 := by
    have hnat : (2285187931 : ℕ)^4117*50000000000000^3093 ≤ 7008903895963^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285187931 10000000000 7008903895963 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261219079/10000000000 : ℝ)^4117 ≤ (2126749877323/5000000000000 : ℝ)^3093 := by
    have hnat : (5261219079 : ℕ)^4117*5000000000000^3093 ≤ 2126749877323^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261219079 10000000000 2126749877323 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345762171/10000000000 : ℝ), (-2285187931/10000000000 : ℝ), (5261219079/10000000000 : ℝ)] ![(135772483283/312500000000 : ℝ), (7008903895963/50000000000000 : ℝ), (2126749877323/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345762171/10000000000 : ℝ)|^4117 ≤ (135772483283/312500000000 : ℝ)^3093
        have hw : |(5345762171/10000000000 : ℝ)|=(5345762171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285187931/10000000000 : ℝ)|^4117 ≤ (7008903895963/50000000000000 : ℝ)^3093
        have hw : |(-2285187931/10000000000 : ℝ)|=(2285187931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261219079/10000000000 : ℝ)|^4117 ≤ (2126749877323/5000000000000 : ℝ)^3093
        have hw : |(5261219079/10000000000 : ℝ)|=(5261219079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26728811/50000000 : ℝ)*x 0 + (657652387/1250000000 : ℝ)*x 1 + (-228518787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26728811/50000000 : ℝ)^4117 ≤ (21723597482143/50000000000000 : ℝ)^3093 := by
    have hnat : (26728811 : ℕ)^4117*50000000000000^3093 ≤ 21723597482143^3093*50000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26728811 50000000 21723597482143 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657652387/1250000000 : ℝ)^4117 ≤ (42534997729401/100000000000000 : ℝ)^3093 := by
    have hnat : (657652387 : ℕ)^4117*100000000000000^3093 ≤ 42534997729401^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657652387 1250000000 42534997729401 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228518787/1000000000 : ℝ)^4117 ≤ (14017807293857/100000000000000 : ℝ)^3093 := by
    have hnat : (228518787 : ℕ)^4117*100000000000000^3093 ≤ 14017807293857^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228518787 1000000000 14017807293857 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26728811/50000000 : ℝ), (657652387/1250000000 : ℝ), (-228518787/1000000000 : ℝ)] ![(21723597482143/50000000000000 : ℝ), (42534997729401/100000000000000 : ℝ), (14017807293857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26728811/50000000 : ℝ)|^4117 ≤ (21723597482143/50000000000000 : ℝ)^3093
        have hw : |(26728811/50000000 : ℝ)|=(26728811/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657652387/1250000000 : ℝ)|^4117 ≤ (42534997729401/100000000000000 : ℝ)^3093
        have hw : |(657652387/1250000000 : ℝ)|=(657652387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228518787/1000000000 : ℝ)|^4117 ≤ (14017807293857/100000000000000 : ℝ)^3093
        have hw : |(-228518787/1000000000 : ℝ)|=(228518787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094737773/2500000000 : ℝ)*x 0 + (849581593/2000000000 : ℝ)*x 1 + (451411731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094737773/2500000000 : ℝ)^4117 ≤ (8328723485891/25000000000000 : ℝ)^3093 := by
    have hnat : (1094737773 : ℕ)^4117*25000000000000^3093 ≤ 8328723485891^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094737773 2500000000 8328723485891 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849581593/2000000000 : ℝ)^4117 ≤ (15997236823107/50000000000000 : ℝ)^3093 := by
    have hnat : (849581593 : ℕ)^4117*50000000000000^3093 ≤ 15997236823107^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849581593 2000000000 15997236823107 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451411731/1000000000 : ℝ)^4117 ≤ (6938126477553/20000000000000 : ℝ)^3093 := by
    have hnat : (451411731 : ℕ)^4117*20000000000000^3093 ≤ 6938126477553^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451411731 1000000000 6938126477553 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094737773/2500000000 : ℝ), (849581593/2000000000 : ℝ), (451411731/1000000000 : ℝ)] ![(8328723485891/25000000000000 : ℝ), (15997236823107/50000000000000 : ℝ), (6938126477553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094737773/2500000000 : ℝ)|^4117 ≤ (8328723485891/25000000000000 : ℝ)^3093
        have hw : |(1094737773/2500000000 : ℝ)|=(1094737773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849581593/2000000000 : ℝ)|^4117 ≤ (15997236823107/50000000000000 : ℝ)^3093
        have hw : |(849581593/2000000000 : ℝ)|=(849581593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451411731/1000000000 : ℝ)|^4117 ≤ (6938126477553/20000000000000 : ℝ)^3093
        have hw : |(451411731/1000000000 : ℝ)|=(451411731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107941129/5000000000 : ℝ)*x 0 + (2630787681/5000000000 : ℝ)*x 1 + (2698684933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107941129/5000000000 : ℝ)^4117 ≤ (3363695890519/25000000000000 : ℝ)^3093 := by
    have hnat : (1107941129 : ℕ)^4117*25000000000000^3093 ≤ 3363695890519^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107941129 5000000000 3363695890519 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630787681/5000000000 : ℝ)^4117 ≤ (1063470790611/2500000000000 : ℝ)^3093 := by
    have hnat : (2630787681 : ℕ)^4117*2500000000000^3093 ≤ 1063470790611^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630787681 5000000000 1063470790611 2500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698684933/5000000000 : ℝ)^4117 ≤ (44006384793567/100000000000000 : ℝ)^3093 := by
    have hnat : (2698684933 : ℕ)^4117*100000000000000^3093 ≤ 44006384793567^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698684933 5000000000 44006384793567 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107941129/5000000000 : ℝ), (2630787681/5000000000 : ℝ), (2698684933/5000000000 : ℝ)] ![(3363695890519/25000000000000 : ℝ), (1063470790611/2500000000000 : ℝ), (44006384793567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107941129/5000000000 : ℝ)|^4117 ≤ (3363695890519/25000000000000 : ℝ)^3093
        have hw : |(-1107941129/5000000000 : ℝ)|=(1107941129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630787681/5000000000 : ℝ)|^4117 ≤ (1063470790611/2500000000000 : ℝ)^3093
        have hw : |(2630787681/5000000000 : ℝ)|=(2630787681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698684933/5000000000 : ℝ)|^4117 ≤ (44006384793567/100000000000000 : ℝ)^3093
        have hw : |(2698684933/5000000000 : ℝ)|=(2698684933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327861999/2500000000 : ℝ)*x 0 + (-1074518891/5000000000 : ℝ)*x 1 + (674671163/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327861999/2500000000 : ℝ)^4117 ≤ (43076373717571/100000000000000 : ℝ)^3093 := by
    have hnat : (1327861999 : ℕ)^4117*100000000000000^3093 ≤ 43076373717571^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327861999 2500000000 43076373717571 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074518891/5000000000 : ℝ)^4117 ≤ (12917247560737/100000000000000 : ℝ)^3093 := by
    have hnat : (1074518891 : ℕ)^4117*100000000000000^3093 ≤ 12917247560737^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074518891 5000000000 12917247560737 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674671163/1250000000 : ℝ)^4117 ≤ (11001594673599/25000000000000 : ℝ)^3093 := by
    have hnat : (674671163 : ℕ)^4117*25000000000000^3093 ≤ 11001594673599^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674671163 1250000000 11001594673599 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327861999/2500000000 : ℝ), (-1074518891/5000000000 : ℝ), (674671163/1250000000 : ℝ)] ![(43076373717571/100000000000000 : ℝ), (12917247560737/100000000000000 : ℝ), (11001594673599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327861999/2500000000 : ℝ)|^4117 ≤ (43076373717571/100000000000000 : ℝ)^3093
        have hw : |(1327861999/2500000000 : ℝ)|=(1327861999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1074518891/5000000000 : ℝ)|^4117 ≤ (12917247560737/100000000000000 : ℝ)^3093
        have hw : |(-1074518891/5000000000 : ℝ)|=(1074518891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674671163/1250000000 : ℝ)|^4117 ≤ (11001594673599/25000000000000 : ℝ)^3093
        have hw : |(674671163/1250000000 : ℝ)|=(674671163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327861997/2500000000 : ℝ)*x 0 + (5397369123/10000000000 : ℝ)*x 1 + (-53725951/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327861997/2500000000 : ℝ)^4117 ≤ (4307637363121/10000000000000 : ℝ)^3093 := by
    have hnat : (1327861997 : ℕ)^4117*10000000000000^3093 ≤ 4307637363121^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327861997 2500000000 4307637363121 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397369123/10000000000 : ℝ)^4117 ≤ (44006376730073/100000000000000 : ℝ)^3093 := by
    have hnat : (5397369123 : ℕ)^4117*100000000000000^3093 ≤ 44006376730073^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397369123 10000000000 44006376730073 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53725951/250000000 : ℝ)^4117 ≤ (807328101557/6250000000000 : ℝ)^3093 := by
    have hnat : (53725951 : ℕ)^4117*6250000000000^3093 ≤ 807328101557^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53725951 250000000 807328101557 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327861997/2500000000 : ℝ), (5397369123/10000000000 : ℝ), (-53725951/250000000 : ℝ)] ![(4307637363121/10000000000000 : ℝ), (44006376730073/100000000000000 : ℝ), (807328101557/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327861997/2500000000 : ℝ)|^4117 ≤ (4307637363121/10000000000000 : ℝ)^3093
        have hw : |(1327861997/2500000000 : ℝ)|=(1327861997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397369123/10000000000 : ℝ)|^4117 ≤ (44006376730073/100000000000000 : ℝ)^3093
        have hw : |(5397369123/10000000000 : ℝ)|=(5397369123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53725951/250000000 : ℝ)|^4117 ≤ (807328101557/6250000000000 : ℝ)^3093
        have hw : |(-53725951/250000000 : ℝ)|=(53725951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s5_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4378961629/10000000000 : ℝ)*x 0 + (4513422719/10000000000 : ℝ)*x 1 + (849721199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378961629/10000000000 : ℝ)^4117 ≤ (16657500324487/50000000000000 : ℝ)^3093 := by
    have hnat : (4378961629 : ℕ)^4117*50000000000000^3093 ≤ 16657500324487^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378961629 10000000000 16657500324487 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513422719/10000000000 : ℝ)^4117 ≤ (2167720467533/6250000000000 : ℝ)^3093 := by
    have hnat : (4513422719 : ℕ)^4117*6250000000000^3093 ≤ 2167720467533^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513422719 10000000000 2167720467533 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849721199/2000000000 : ℝ)^4117 ≤ (32001471852161/100000000000000 : ℝ)^3093 := by
    have hnat : (849721199 : ℕ)^4117*100000000000000^3093 ≤ 32001471852161^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849721199 2000000000 32001471852161 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378961629/10000000000 : ℝ), (4513422719/10000000000 : ℝ), (849721199/2000000000 : ℝ)] ![(16657500324487/50000000000000 : ℝ), (2167720467533/6250000000000 : ℝ), (32001471852161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378961629/10000000000 : ℝ)|^4117 ≤ (16657500324487/50000000000000 : ℝ)^3093
        have hw : |(4378961629/10000000000 : ℝ)|=(4378961629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513422719/10000000000 : ℝ)|^4117 ≤ (2167720467533/6250000000000 : ℝ)^3093
        have hw : |(4513422719/10000000000 : ℝ)|=(4513422719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849721199/2000000000 : ℝ)|^4117 ≤ (32001471852161/100000000000000 : ℝ)^3093
        have hw : |(849721199/2000000000 : ℝ)|=(849721199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1371/12500 : ℝ) ^ (8233/2048 : ℝ) ≤ (34612548485961/250000000000000000 : ℝ) := by
    have hpowers : (1371/12500 : ℝ)^8233 ≤ (34612548485961/250000000000000000 : ℝ)^2048 := by
      have hnat : (1371 : ℕ)^8233*250000000000000000^2048 ≤ 34612548485961^2048*12500^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1371 12500 34612548485961 250000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1371/12500 : ℝ)) (X := (34612548485961/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (8233/2048 : ℝ) ≤ (39634572268914291/100000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^8233 ≤ (39634572268914291/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1781 : ℕ)^8233*100000000000000000000^2048 ≤ 39634572268914291^2048*12500^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 39634572268914291 100000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (39634572268914291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (125034612548485961/125000000000000000 : ℝ) ≤ (2000137746391517/2000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (125034612548485961/125000000000000000 : ℝ)^2048 ≤ (2000137746391517/2000000000000000 : ℝ)^8233 := by
      have hnat : (125034612548485961 : ℕ)^2048*2000000000000000^8233 ≤ 2000137746391517^8233*125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125034612548485961 125000000000000000 2000137746391517 2000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000137746391517/2000000000000000 : ℝ)) (X := (125034612548485961/125000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053479591663298691/100000000000000000000 : ℝ) ≤ (5000665032241091/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (100053479591663298691/100000000000000000000 : ℝ)^2048 ≤ (5000665032241091/5000000000000000 : ℝ)^8233 := by
      have hnat : (100053479591663298691 : ℕ)^2048*5000000000000000^8233 ≤ 5000665032241091^8233*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053479591663298691 100000000000000000000 5000665032241091 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000665032241091/5000000000000000 : ℝ)) (X := (100053479591663298691/100000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039634572268914291/50000000000000000000 : ℝ) ≤ (10001971397006779/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50039634572268914291/50000000000000000000 : ℝ)^2048 ≤ (10001971397006779/10000000000000000 : ℝ)^8233 := by
      have hnat : (50039634572268914291 : ℕ)^2048*10000000000000000^8233 ≤ 10001971397006779^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039634572268914291 50000000000000000000 10001971397006779 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001971397006779/10000000000000000 : ℝ)) (X := (50039634572268914291/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(34612548485961/250000000000000000 : ℝ) ≤ ((1024630961580041219/1025000000000000000 : ℝ)+2*(641332524597/328000000000000 : ℝ)*(1371/12500 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1024630961580041219/1025000000000000000 : ℝ)+2*(641332524597/328000000000000 : ℝ)*(1371/12500 : ℝ)=(2000137746391517/2000000000000000 : ℝ) by norm_num, show 1+2*(34612548485961/250000000000000000 : ℝ)=(125034612548485961/125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39634572268914291/100000000000000000000 : ℝ)+(34612548485961/250000000000000000 : ℝ) ≤ ((1024630961580041219/1025000000000000000 : ℝ)+(641332524597/328000000000000 : ℝ)*((1781/12500 : ℝ)+(1371/12500 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (1024630961580041219/1025000000000000000 : ℝ)+(641332524597/328000000000000 : ℝ)*((1781/12500 : ℝ)+(1371/12500 : ℝ))=(5000665032241091/5000000000000000 : ℝ) by norm_num, show 1+(39634572268914291/100000000000000000000 : ℝ)+(34612548485961/250000000000000000 : ℝ)=(100053479591663298691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39634572268914291/100000000000000000000 : ℝ) ≤ ((1024630961580041219/1025000000000000000 : ℝ)+2*(641332524597/328000000000000 : ℝ)*(1781/12500 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1024630961580041219/1025000000000000000 : ℝ)+2*(641332524597/328000000000000 : ℝ)*(1781/12500 : ℝ)=(10001971397006779/10000000000000000 : ℝ) by norm_num, show 1+2*(39634572268914291/100000000000000000000 : ℝ)=(50039634572268914291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1024630961580041219/1025000000000000000 : ℝ)*(X 1 0+X 2 0)+(641332524597/328000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1024630961580041219/1025000000000000000 : ℝ)) (alpha := (641332524597/328000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1024630961580041219/1025000000000000000 : ℝ)*(X 0 1+X 2 1)+(641332524597/328000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1024630961580041219/1025000000000000000 : ℝ)) (alpha := (641332524597/328000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1024630961580041219/1025000000000000000 : ℝ)*(X 0 2+X 1 2)+(641332524597/328000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (1371/12500 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (1024630961580041219/1025000000000000000 : ℝ)) (alpha := (641332524597/328000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1107938427/5000000000 : ℝ)*X 0 0+(5397727091/10000000000 : ℝ)*X 0 1+(5261219161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345762171/10000000000 : ℝ)*X 1 0+(-2285187931/10000000000 : ℝ)*X 1 1+(5261219079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26728811/50000000 : ℝ)*X 2 0+(657652387/1250000000 : ℝ)*X 2 1+(-228518787/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094737773/2500000000 : ℝ)*X 0 0+(849581593/2000000000 : ℝ)*X 0 1+(451411731/1000000000 : ℝ)*X 0 2+(1094737773/2500000000 : ℝ)*X 1 0+(849581593/2000000000 : ℝ)*X 1 1+(451411731/1000000000 : ℝ)*X 1 2+(1094737773/2500000000 : ℝ)*X 2 0+(849581593/2000000000 : ℝ)*X 2 1+(451411731/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107941129/5000000000 : ℝ)*X 0 0+(2630787681/5000000000 : ℝ)*X 0 1+(2698684933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327861999/2500000000 : ℝ)*X 1 0+(-1074518891/5000000000 : ℝ)*X 1 1+(674671163/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327861997/2500000000 : ℝ)*X 2 0+(5397369123/10000000000 : ℝ)*X 2 1+(-53725951/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378961629/10000000000 : ℝ)*X 0 0+(4513422719/10000000000 : ℝ)*X 0 1+(849721199/2000000000 : ℝ)*X 0 2+(4378961629/10000000000 : ℝ)*X 1 0+(4513422719/10000000000 : ℝ)*X 1 1+(849721199/2000000000 : ℝ)*X 1 2+(4378961629/10000000000 : ℝ)*X 2 0+(4513422719/10000000000 : ℝ)*X 2 1+(849721199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46496343277591936578106713/25625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536034869/100000000000000 : ℝ)*(base19) + (286825739/50000000000000 : ℝ)*(base23) + (1177423/20000000000000 : ℝ)*(upper4) + (54450569/100000000000000 : ℝ)*(upper5) + (2770516321100483/50000000000000 : ℝ)*(major0) + (2770516321100483/50000000000000 : ℝ)*(major1) + (2770516321100483/50000000000000 : ℝ)*(major2) + (3662797070364507/50000000000000 : ℝ)*(sp0) + (3662803924789609/50000000000000 : ℝ)*(sp1) + (7325609196752637/100000000000000 : ℝ)*(sp2) + (150257966131873/4000000000000 : ℝ)*(sp3) + (15629675101/100000000000000 : ℝ)*(sp4) + (346197507/25000000000000 : ℝ)*(sp5) + (6300217937/100000000000000 : ℝ)*(sp7) + (1878227726757381/50000000000000 : ℝ)*(f.failure) + (1465121954080823/20000000000000 : ℝ)*(f.sum) + (34806063556551/8200000000000000000000000000 : ℝ)*base65 + (1907979092671307/312500000000000000000000000000 : ℝ)*base68 + (2067766182016193/312500000000000000000000000000 : ℝ)*base69 + (5788843790141193/312500000000000000000000000000 : ℝ)*base71 + (9864614906449/8200000000000000000000000000 : ℝ)*base74 + (2379435865141193/312500000000000000000000000000 : ℝ)*base75 + (6204039029516193/312500000000000000000000000000 : ℝ)*base77 + (551778308578693/312500000000000000000000000000 : ℝ)*base79 + (18551644894649/8200000000000000000000000000 : ℝ)*base82 + (23/152587890625000000 : ℝ)*base89 + (23/152587890625000000 : ℝ)*base91 + (23/152587890625000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79563559093098014619786909/6406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (750596487/100000000000000 : ℝ)*(base19) + (153608043/20000000000000 : ℝ)*(base23) + (145863267/100000000000000 : ℝ)*(lower3) + (14353631/20000000000000 : ℝ)*(lower4) + (696268268207413/12500000000000 : ℝ)*(major0) + (696268268207413/12500000000000 : ℝ)*(major1) + (696268268207413/12500000000000 : ℝ)*(major2) + (13801931111/100000000000000 : ℝ)*(sp0) + (9746109067/50000000000000 : ℝ)*(sp1) + (299415543/10000000000000 : ℝ)*(sp2) + (7364085582616809/100000000000000 : ℝ)*(sp4) + (7364079141733299/100000000000000 : ℝ)*(sp5) + (294563824894091/4000000000000 : ℝ)*(sp6) + (3776192492781427/100000000000000 : ℝ)*(sp7) + (3776192492781427/100000000000000 : ℝ)*(f.failure) + (92051242306849/1250000000000 : ℝ)*(f.sum) + (8509660850211/2050000000000000000000000000 : ℝ)*base65 + (606738877332223/78125000000000000000000000000 : ℝ)*base67 + (1024924630613473/78125000000000000000000000000 : ℝ)*base69 + (779003644564549/39062500000000000000000000000 : ℝ)*base71 + (5214292466489/2050000000000000000000000000 : ℝ)*base74 + (11169955959913/19531250000000000000000000000 : ℝ)*base76 + (254007857790087/19531250000000000000000000000 : ℝ)*base77 + (1638574259074027/78125000000000000000000000000 : ℝ)*base80 + (1300026719311/2050000000000000000000000000 : ℝ)*base81 + (169027/39062500000000000000 : ℝ)*base90 + (169027/39062500000000000000 : ℝ)*base92 + (169027/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1041_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1041_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1041_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1041_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1041_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
