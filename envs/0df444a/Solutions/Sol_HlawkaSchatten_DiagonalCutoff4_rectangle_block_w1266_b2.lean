-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:50.768224+00:00
-- url     : https://prove2.me/submissions/ec5138b5-846a-4f44-b7e6-3d95caf36e33

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
theorem support_rectangle_w1266_s6_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108947373/10000000000 : ℝ)*x 0 + (5390914257/10000000000 : ℝ)*x 1 + (2633685869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108947373/10000000000 : ℝ)^8459 ≤ (12827378388531/100000000000000 : ℝ)^6411 := by
    have hnat : (2108947373 : ℕ)^8459*100000000000000^6411 ≤ 12827378388531^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108947373 10000000000 12827378388531 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390914257/10000000000 : ℝ)^8459 ≤ (44252899622351/100000000000000 : ℝ)^6411 := by
    have hnat : (5390914257 : ℕ)^8459*100000000000000^6411 ≤ 44252899622351^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390914257 10000000000 44252899622351 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633685869/5000000000 : ℝ)^8459 ≤ (42919721966819/100000000000000 : ℝ)^6411 := by
    have hnat : (2633685869 : ℕ)^8459*100000000000000^6411 ≤ 42919721966819^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633685869 5000000000 42919721966819 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108947373/10000000000 : ℝ), (5390914257/10000000000 : ℝ), (2633685869/5000000000 : ℝ)] ![(12827378388531/100000000000000 : ℝ), (44252899622351/100000000000000 : ℝ), (42919721966819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108947373/10000000000 : ℝ)|^8459 ≤ (12827378388531/100000000000000 : ℝ)^6411
        have hw : |(-2108947373/10000000000 : ℝ)|=(2108947373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390914257/10000000000 : ℝ)|^8459 ≤ (44252899622351/100000000000000 : ℝ)^6411
        have hw : |(5390914257/10000000000 : ℝ)|=(5390914257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633685869/5000000000 : ℝ)|^8459 ≤ (42919721966819/100000000000000 : ℝ)^6411
        have hw : |(2633685869/5000000000 : ℝ)|=(2633685869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336055063/2500000000 : ℝ)*x 0 + (-2171583393/10000000000 : ℝ)*x 1 + (2633685867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336055063/2500000000 : ℝ)^8459 ≤ (43747853266829/100000000000000 : ℝ)^6411 := by
    have hnat : (1336055063 : ℕ)^8459*100000000000000^6411 ≤ 43747853266829^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336055063 2500000000 43747853266829 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171583393/10000000000 : ℝ)^8459 ≤ (66662123969/500000000000 : ℝ)^6411 := by
    have hnat : (2171583393 : ℕ)^8459*500000000000^6411 ≤ 66662123969^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171583393 10000000000 66662123969 500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633685867/5000000000 : ℝ)^8459 ≤ (8583944384763/20000000000000 : ℝ)^6411 := by
    have hnat : (2633685867 : ℕ)^8459*20000000000000^6411 ≤ 8583944384763^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633685867 5000000000 8583944384763 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336055063/2500000000 : ℝ), (-2171583393/10000000000 : ℝ), (2633685867/5000000000 : ℝ)] ![(43747853266829/100000000000000 : ℝ), (66662123969/500000000000 : ℝ), (8583944384763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336055063/2500000000 : ℝ)|^8459 ≤ (43747853266829/100000000000000 : ℝ)^6411
        have hw : |(1336055063/2500000000 : ℝ)|=(1336055063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171583393/10000000000 : ℝ)|^8459 ≤ (66662123969/500000000000 : ℝ)^6411
        have hw : |(-2171583393/10000000000 : ℝ)|=(2171583393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633685867/5000000000 : ℝ)|^8459 ≤ (8583944384763/20000000000000 : ℝ)^6411
        have hw : |(2633685867/5000000000 : ℝ)|=(2633685867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672110129/5000000000 : ℝ)*x 0 + (1316842933/2500000000 : ℝ)*x 1 + (-542895847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672110129/5000000000 : ℝ)^8459 ≤ (8749570666327/20000000000000 : ℝ)^6411 := by
    have hnat : (2672110129 : ℕ)^8459*20000000000000^6411 ≤ 8749570666327^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672110129 5000000000 8749570666327 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316842933/2500000000 : ℝ)^8459 ≤ (5364965237789/12500000000000 : ℝ)^6411 := by
    have hnat : (1316842933 : ℕ)^8459*12500000000000^6411 ≤ 5364965237789^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316842933 2500000000 5364965237789 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542895847/2500000000 : ℝ)^8459 ≤ (833276547081/6250000000000 : ℝ)^6411 := by
    have hnat : (542895847 : ℕ)^8459*6250000000000^6411 ≤ 833276547081^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542895847 2500000000 833276547081 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672110129/5000000000 : ℝ), (1316842933/2500000000 : ℝ), (-542895847/2500000000 : ℝ)] ![(8749570666327/20000000000000 : ℝ), (5364965237789/12500000000000 : ℝ), (833276547081/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672110129/5000000000 : ℝ)|^8459 ≤ (8749570666327/20000000000000 : ℝ)^6411
        have hw : |(2672110129/5000000000 : ℝ)|=(2672110129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316842933/2500000000 : ℝ)|^8459 ≤ (5364965237789/12500000000000 : ℝ)^6411
        have hw : |(1316842933/2500000000 : ℝ)|=(1316842933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542895847/2500000000 : ℝ)|^8459 ≤ (833276547081/6250000000000 : ℝ)^6411
        have hw : |(-542895847/2500000000 : ℝ)|=(542895847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108687099/250000000 : ℝ)*x 0 + (131979937/312500000 : ℝ)*x 1 + (4475134599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108687099/250000000 : ℝ)^8459 ≤ (33317528074229/100000000000000 : ℝ)^6411 := by
    have hnat : (108687099 : ℕ)^8459*100000000000000^6411 ≤ 33317528074229^6411*250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108687099 250000000 33317528074229 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131979937/312500000 : ℝ)^8459 ≤ (6413630738177/20000000000000 : ℝ)^6411 := by
    have hnat : (131979937 : ℕ)^8459*20000000000000^6411 ≤ 6413630738177^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131979937 312500000 6413630738177 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475134599/10000000000 : ℝ)^8459 ≤ (8653579555043/25000000000000 : ℝ)^6411 := by
    have hnat : (4475134599 : ℕ)^8459*25000000000000^6411 ≤ 8653579555043^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475134599 10000000000 8653579555043 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108687099/250000000 : ℝ), (131979937/312500000 : ℝ), (4475134599/10000000000 : ℝ)] ![(33317528074229/100000000000000 : ℝ), (6413630738177/20000000000000 : ℝ), (8653579555043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108687099/250000000 : ℝ)|^8459 ≤ (33317528074229/100000000000000 : ℝ)^6411
        have hw : |(108687099/250000000 : ℝ)|=(108687099/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131979937/312500000 : ℝ)|^8459 ≤ (6413630738177/20000000000000 : ℝ)^6411
        have hw : |(131979937/312500000 : ℝ)|=(131979937/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475134599/10000000000 : ℝ)|^8459 ≤ (8653579555043/25000000000000 : ℝ)^6411
        have hw : |(4475134599/10000000000 : ℝ)|=(4475134599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108952011/10000000000 : ℝ)*x 0 + (5267684383/10000000000 : ℝ)*x 1 + (5390600477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108952011/10000000000 : ℝ)^8459 ≤ (20042836891/156250000000 : ℝ)^6411 := by
    have hnat : (2108952011 : ℕ)^8459*156250000000^6411 ≤ 20042836891^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108952011 10000000000 20042836891 156250000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267684383/10000000000 : ℝ)^8459 ≤ (42923083301711/100000000000000 : ℝ)^6411 := by
    have hnat : (5267684383 : ℕ)^8459*100000000000000^6411 ≤ 42923083301711^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267684383 10000000000 42923083301711 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390600477/10000000000 : ℝ)^8459 ≤ (22124750535731/50000000000000 : ℝ)^6411 := by
    have hnat : (5390600477 : ℕ)^8459*50000000000000^6411 ≤ 22124750535731^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390600477 10000000000 22124750535731 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108952011/10000000000 : ℝ), (5267684383/10000000000 : ℝ), (5390600477/10000000000 : ℝ)] ![(20042836891/156250000000 : ℝ), (42923083301711/100000000000000 : ℝ), (22124750535731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108952011/10000000000 : ℝ)|^8459 ≤ (20042836891/156250000000 : ℝ)^6411
        have hw : |(-2108952011/10000000000 : ℝ)|=(2108952011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267684383/10000000000 : ℝ)|^8459 ≤ (42923083301711/100000000000000 : ℝ)^6411
        have hw : |(5267684383/10000000000 : ℝ)|=(5267684383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390600477/10000000000 : ℝ)|^8459 ≤ (22124750535731/50000000000000 : ℝ)^6411
        have hw : |(5390600477/10000000000 : ℝ)|=(5390600477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312647201/10000000000 : ℝ)*x 0 + (-2048354643/10000000000 : ℝ)*x 1 + (5390600479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312647201/10000000000 : ℝ)^8459 ≤ (43407153657773/100000000000000 : ℝ)^6411 := by
    have hnat : (5312647201 : ℕ)^8459*100000000000000^6411 ≤ 43407153657773^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312647201 10000000000 43407153657773 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048354643/10000000000 : ℝ)^8459 ≤ (1542918154691/12500000000000 : ℝ)^6411 := by
    have hnat : (2048354643 : ℕ)^8459*12500000000000^6411 ≤ 1542918154691^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048354643 10000000000 1542918154691 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390600479/10000000000 : ℝ)^8459 ≤ (11062375273281/25000000000000 : ℝ)^6411 := by
    have hnat : (5390600479 : ℕ)^8459*25000000000000^6411 ≤ 11062375273281^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390600479 10000000000 11062375273281 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312647201/10000000000 : ℝ), (-2048354643/10000000000 : ℝ), (5390600479/10000000000 : ℝ)] ![(43407153657773/100000000000000 : ℝ), (1542918154691/12500000000000 : ℝ), (11062375273281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312647201/10000000000 : ℝ)|^8459 ≤ (43407153657773/100000000000000 : ℝ)^6411
        have hw : |(5312647201/10000000000 : ℝ)|=(5312647201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048354643/10000000000 : ℝ)|^8459 ≤ (1542918154691/12500000000000 : ℝ)^6411
        have hw : |(-2048354643/10000000000 : ℝ)|=(2048354643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390600479/10000000000 : ℝ)|^8459 ≤ (11062375273281/25000000000000 : ℝ)^6411
        have hw : |(5390600479/10000000000 : ℝ)|=(5390600479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323601/5000000000 : ℝ)*x 0 + (2695300239/5000000000 : ℝ)*x 1 + (-1024177321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323601/5000000000 : ℝ)^8459 ≤ (43407153668553/100000000000000 : ℝ)^6411 := by
    have hnat : (2656323601 : ℕ)^8459*100000000000000^6411 ≤ 43407153668553^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323601 5000000000 43407153668553 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695300239/5000000000 : ℝ)^8459 ≤ (44249501082293/100000000000000 : ℝ)^6411 := by
    have hnat : (2695300239 : ℕ)^8459*100000000000000^6411 ≤ 44249501082293^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695300239 5000000000 44249501082293 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024177321/5000000000 : ℝ)^8459 ≤ (12343345229577/100000000000000 : ℝ)^6411 := by
    have hnat : (1024177321 : ℕ)^8459*100000000000000^6411 ≤ 12343345229577^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024177321 5000000000 12343345229577 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323601/5000000000 : ℝ), (2695300239/5000000000 : ℝ), (-1024177321/5000000000 : ℝ)] ![(43407153668553/100000000000000 : ℝ), (44249501082293/100000000000000 : ℝ), (12343345229577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323601/5000000000 : ℝ)|^8459 ≤ (43407153668553/100000000000000 : ℝ)^6411
        have hw : |(2656323601/5000000000 : ℝ)|=(2656323601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695300239/5000000000 : ℝ)|^8459 ≤ (44249501082293/100000000000000 : ℝ)^6411
        have hw : |(2695300239/5000000000 : ℝ)|=(2695300239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024177321/5000000000 : ℝ)|^8459 ≤ (12343345229577/100000000000000 : ℝ)^6411
        have hw : |(-1024177321/5000000000 : ℝ)|=(1024177321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s6_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434749341/1000000000 : ℝ)*x 0 + (4474497439/10000000000 : ℝ)*x 1 + (131999921/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434749341/1000000000 : ℝ)^8459 ≤ (1332704945227/4000000000000 : ℝ)^6411 := by
    have hnat : (434749341 : ℕ)^8459*4000000000000^6411 ≤ 1332704945227^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434749341 1000000000 1332704945227 4000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474497439/10000000000 : ℝ)^8459 ≤ (34607815702299/100000000000000 : ℝ)^6411 := by
    have hnat : (4474497439 : ℕ)^8459*100000000000000^6411 ≤ 34607815702299^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474497439 10000000000 34607815702299 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131999921/312500000 : ℝ)^8459 ≤ (32074560653823/100000000000000 : ℝ)^6411 := by
    have hnat : (131999921 : ℕ)^8459*100000000000000^6411 ≤ 32074560653823^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131999921 312500000 32074560653823 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434749341/1000000000 : ℝ), (4474497439/10000000000 : ℝ), (131999921/312500000 : ℝ)] ![(1332704945227/4000000000000 : ℝ), (34607815702299/100000000000000 : ℝ), (32074560653823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434749341/1000000000 : ℝ)|^8459 ≤ (1332704945227/4000000000000 : ℝ)^6411
        have hw : |(434749341/1000000000 : ℝ)|=(434749341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474497439/10000000000 : ℝ)|^8459 ≤ (34607815702299/100000000000000 : ℝ)^6411
        have hw : |(4474497439/10000000000 : ℝ)|=(4474497439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131999921/312500000 : ℝ)|^8459 ≤ (32074560653823/100000000000000 : ℝ)^6411
        have hw : |(131999921/312500000 : ℝ)|=(131999921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (707/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11503/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (707/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2297/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (707/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2297/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (707/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2297/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (707/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2297/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (707/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2297/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (707/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2297/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2297/20000 : ℝ) ^ (4229/1024 : ℝ) ≤ (1313563792668893/10000000000000000000 : ℝ) := by
    have hpowers : (2297/20000 : ℝ)^4229 ≤ (1313563792668893/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2297 : ℕ)^4229*10000000000000000000^1024 ≤ 1313563792668893^1024*20000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2297 20000 1313563792668893 10000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2297/20000 : ℝ)) (X := (1313563792668893/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (707/5000 : ℝ) ^ (4229/1024 : ℝ) ≤ (15503352514722377/50000000000000000000 : ℝ) := by
    have hpowers : (707/5000 : ℝ)^4229 ≤ (15503352514722377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (707 : ℕ)^4229*50000000000000000000^1024 ≤ 15503352514722377^1024*5000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 5000 15503352514722377 50000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/5000 : ℝ)) (X := (15503352514722377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001313563792668893/5000000000000000000 : ℝ) ≤ (10000636063107393/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (5001313563792668893/5000000000000000000 : ℝ)^1024 ≤ (10000636063107393/10000000000000000 : ℝ)^4229 := by
      have hnat : (5001313563792668893 : ℕ)^1024*10000000000000000^4229 ≤ 10000636063107393^4229*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001313563792668893 5000000000000000000 10000636063107393 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000636063107393/10000000000000000 : ℝ)) (X := (5001313563792668893/5000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011035585739033421/25000000000000000000 : ℝ) ≤ (5000534336725991/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25011035585739033421/25000000000000000000 : ℝ)^1024 ≤ (5000534336725991/5000000000000000 : ℝ)^4229 := by
      have hnat : (25011035585739033421 : ℕ)^1024*5000000000000000^4229 ≤ 5000534336725991^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011035585739033421 25000000000000000000 5000534336725991 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000534336725991/5000000000000000 : ℝ)) (X := (25011035585739033421/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015503352514722377/25000000000000000000 : ℝ) ≤ (10001501283796571/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25015503352514722377/25000000000000000000 : ℝ)^1024 ≤ (10001501283796571/10000000000000000 : ℝ)^4229 := by
      have hnat : (25015503352514722377 : ℕ)^1024*10000000000000000^4229 ≤ 10001501283796571^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015503352514722377 25000000000000000000 10001501283796571 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001501283796571/10000000000000000 : ℝ)) (X := (25015503352514722377/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1313563792668893/10000000000000000000 : ℝ) ≤ ((5308350337586983817/5310000000000000000 : ℝ)+2*(432610344589/265500000000000 : ℝ)*(2297/20000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (5308350337586983817/5310000000000000000 : ℝ)+2*(432610344589/265500000000000 : ℝ)*(2297/20000 : ℝ)=(10000636063107393/10000000000000000 : ℝ) by norm_num, show 1+2*(1313563792668893/10000000000000000000 : ℝ)=(5001313563792668893/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15503352514722377/50000000000000000000 : ℝ)+(1313563792668893/10000000000000000000 : ℝ) ≤ ((5308350337586983817/5310000000000000000 : ℝ)+(432610344589/265500000000000 : ℝ)*((707/5000 : ℝ)+(2297/20000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (5308350337586983817/5310000000000000000 : ℝ)+(432610344589/265500000000000 : ℝ)*((707/5000 : ℝ)+(2297/20000 : ℝ))=(5000534336725991/5000000000000000 : ℝ) by norm_num, show 1+(15503352514722377/50000000000000000000 : ℝ)+(1313563792668893/10000000000000000000 : ℝ)=(25011035585739033421/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15503352514722377/50000000000000000000 : ℝ) ≤ ((5308350337586983817/5310000000000000000 : ℝ)+2*(432610344589/265500000000000 : ℝ)*(707/5000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (5308350337586983817/5310000000000000000 : ℝ)+2*(432610344589/265500000000000 : ℝ)*(707/5000 : ℝ)=(10001501283796571/10000000000000000 : ℝ) by norm_num, show 1+2*(15503352514722377/50000000000000000000 : ℝ)=(25015503352514722377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5308350337586983817/5310000000000000000 : ℝ)*(X 1 0+X 2 0)+(432610344589/265500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (707/5000 : ℝ)) (c := (5308350337586983817/5310000000000000000 : ℝ)) (alpha := (432610344589/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5308350337586983817/5310000000000000000 : ℝ)*(X 0 1+X 2 1)+(432610344589/265500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (707/5000 : ℝ)) (c := (5308350337586983817/5310000000000000000 : ℝ)) (alpha := (432610344589/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5308350337586983817/5310000000000000000 : ℝ)*(X 0 2+X 1 2)+(432610344589/265500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (707/5000 : ℝ)) (c := (5308350337586983817/5310000000000000000 : ℝ)) (alpha := (432610344589/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108947373/10000000000 : ℝ)*X 0 0+(5390914257/10000000000 : ℝ)*X 0 1+(2633685869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336055063/2500000000 : ℝ)*X 1 0+(-2171583393/10000000000 : ℝ)*X 1 1+(2633685867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672110129/5000000000 : ℝ)*X 2 0+(1316842933/2500000000 : ℝ)*X 2 1+(-542895847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108687099/250000000 : ℝ)*X 0 0+(131979937/312500000 : ℝ)*X 0 1+(4475134599/10000000000 : ℝ)*X 0 2+(108687099/250000000 : ℝ)*X 1 0+(131979937/312500000 : ℝ)*X 1 1+(4475134599/10000000000 : ℝ)*X 1 2+(108687099/250000000 : ℝ)*X 2 0+(131979937/312500000 : ℝ)*X 2 1+(4475134599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108952011/10000000000 : ℝ)*X 0 0+(5267684383/10000000000 : ℝ)*X 0 1+(5390600477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312647201/10000000000 : ℝ)*X 1 0+(-2048354643/10000000000 : ℝ)*X 1 1+(5390600479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656323601/5000000000 : ℝ)*X 2 0+(2695300239/5000000000 : ℝ)*X 2 1+(-1024177321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434749341/1000000000 : ℝ)*X 0 0+(4474497439/10000000000 : ℝ)*X 0 1+(131999921/312500000 : ℝ)*X 0 2+(434749341/1000000000 : ℝ)*X 1 0+(4474497439/10000000000 : ℝ)*X 1 1+(131999921/312500000 : ℝ)*X 1 2+(434749341/1000000000 : ℝ)*X 2 0+(4474497439/10000000000 : ℝ)*X 2 1+(131999921/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319604505107866117472690973/29500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2087254813/100000000000000 : ℝ)*(base19) + (39019573/2000000000000 : ℝ)*(base23) + (971071/1250000000000 : ℝ)*(lower2) + (135303997/50000000000000 : ℝ)*(upper3) + (87122423/50000000000000 : ℝ)*(upper5) + (6033165331171393/100000000000000 : ℝ)*(major0) + (6033165331171393/100000000000000 : ℝ)*(major1) + (6033165331171393/100000000000000 : ℝ)*(major2) + (8094439325192293/100000000000000 : ℝ)*(sp0) + (8094495176882877/100000000000000 : ℝ)*(sp1) + (8094495313159041/100000000000000 : ℝ)*(sp2) + (1985901202683037/50000000000000 : ℝ)*(sp3) + (57938945397/100000000000000 : ℝ)*(sp4) + (30631703973/100000000000000 : ℝ)*(sp7) + (1985916518535023/50000000000000 : ℝ)*(f.failure) + (8094497264137691/100000000000000 : ℝ)*(f.sum) + (114970449127/13275000000000000000000000000 : ℝ)*base65 + (5937329713928887081/531000000000000000000000000000000 : ℝ)*base67 + (3818000458958887081/531000000000000000000000000000000 : ℝ)*base69 + (6717475094999887081/531000000000000000000000000000000 : ℝ)*base71 + (55627378316573/13275000000000000000000000000 : ℝ)*base74 + (5224732601106112919/531000000000000000000000000000000 : ℝ)*base76 + (2791989853205887081/531000000000000000000000000000000 : ℝ)*base77 + (11753876568531112919/531000000000000000000000000000000 : ℝ)*base80 + (3858674970127/13275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (9410681/1000000000000000000000 : ℝ)*base90 + (9410681/1000000000000000000000 : ℝ)*base92 + (9410681/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18706984470239420202893/2212500000000000000000000000 : ℝ) := by norm_num
    linear_combination (150407587/10000000000000 : ℝ)*(base19) + (1638273159/100000000000000 : ℝ)*(base23) + (85017557/50000000000000 : ℝ)*(upper3) + (7514753/12500000000000 : ℝ)*(lower4) + (171840673/100000000000000 : ℝ)*(upper5) + (1515955726771381/25000000000000 : ℝ)*(major0) + (1515955726771381/25000000000000 : ℝ)*(major1) + (1515955726771381/25000000000000 : ℝ)*(major2) + (21297006257/50000000000000 : ℝ)*(sp1) + (45876138701/100000000000000 : ℝ)*(sp2) + (2033907398803791/25000000000000 : ℝ)*(sp4) + (406779274856339/5000000000000 : ℝ)*(sp5) + (1016947760100413/12500000000000 : ℝ)*(sp6) + (399201593711807/10000000000000 : ℝ)*(sp7) + (399201593711807/10000000000000 : ℝ)*(f.failure) + (2033907398803791/25000000000000 : ℝ)*(f.sum) + (23976767147441/3318750000000000000000000000 : ℝ)*base66 + (417993671003421277/132750000000000000000000000000000 : ℝ)*base67 + (606983775876921277/132750000000000000000000000000000 : ℝ)*base69 + (1878460322858078723/132750000000000000000000000000000 : ℝ)*base72 + (1245166413617/1659375000000000000000000000 : ℝ)*base73 + (362300128550078723/132750000000000000000000000000000 : ℝ)*base76 + (372902156717421277/132750000000000000000000000000000 : ℝ)*base77 + (2395960599144578723/132750000000000000000000000000000 : ℝ)*base80 + (4539878956933/1659375000000000000000000000 : ℝ)*base82 + (1843671/200000000000000000000 : ℝ)*base89 + (1843671/200000000000000000000 : ℝ)*base91 + (1843671/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (707/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s7_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108962363/10000000000 : ℝ)*x 0 + (5390743357/10000000000 : ℝ)*x 1 + (2633766359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108962363/10000000000 : ℝ)^8459 ≤ (641374934453/5000000000000 : ℝ)^6411 := by
    have hnat : (2108962363 : ℕ)^8459*5000000000000^6411 ≤ 641374934453^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108962363 10000000000 641374934453 5000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390743357/10000000000 : ℝ)^8459 ≤ (22125524298387/50000000000000 : ℝ)^6411 := by
    have hnat : (5390743357 : ℕ)^8459*50000000000000^6411 ≤ 22125524298387^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390743357 10000000000 22125524298387 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633766359/5000000000 : ℝ)^8459 ≤ (42921452700407/100000000000000 : ℝ)^6411 := by
    have hnat : (2633766359 : ℕ)^8459*100000000000000^6411 ≤ 42921452700407^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633766359 5000000000 42921452700407 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108962363/10000000000 : ℝ), (5390743357/10000000000 : ℝ), (2633766359/5000000000 : ℝ)] ![(641374934453/5000000000000 : ℝ), (22125524298387/50000000000000 : ℝ), (42921452700407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108962363/10000000000 : ℝ)|^8459 ≤ (641374934453/5000000000000 : ℝ)^6411
        have hw : |(-2108962363/10000000000 : ℝ)|=(2108962363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390743357/10000000000 : ℝ)|^8459 ≤ (22125524298387/50000000000000 : ℝ)^6411
        have hw : |(5390743357/10000000000 : ℝ)|=(5390743357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633766359/5000000000 : ℝ)|^8459 ≤ (42921452700407/100000000000000 : ℝ)^6411
        have hw : |(2633766359/5000000000 : ℝ)|=(2633766359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344176709/10000000000 : ℝ)*x 0 + (-271428477/1250000000 : ℝ)*x 1 + (5267532701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344176709/10000000000 : ℝ)^8459 ≤ (21873691478839/50000000000000 : ℝ)^6411 := by
    have hnat : (5344176709 : ℕ)^8459*50000000000000^6411 ≤ 21873691478839^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344176709 10000000000 21873691478839 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271428477/1250000000 : ℝ)^8459 ≤ (6665582257977/50000000000000 : ℝ)^6411 := by
    have hnat : (271428477 : ℕ)^8459*50000000000000^6411 ≤ 6665582257977^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271428477 1250000000 6665582257977 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267532701/10000000000 : ℝ)^8459 ≤ (8584290503527/20000000000000 : ℝ)^6411 := by
    have hnat : (5267532701 : ℕ)^8459*20000000000000^6411 ≤ 8584290503527^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267532701 10000000000 8584290503527 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344176709/10000000000 : ℝ), (-271428477/1250000000 : ℝ), (5267532701/10000000000 : ℝ)] ![(21873691478839/50000000000000 : ℝ), (6665582257977/50000000000000 : ℝ), (8584290503527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344176709/10000000000 : ℝ)|^8459 ≤ (21873691478839/50000000000000 : ℝ)^6411
        have hw : |(5344176709/10000000000 : ℝ)|=(5344176709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271428477/1250000000 : ℝ)|^8459 ≤ (6665582257977/50000000000000 : ℝ)^6411
        have hw : |(-271428477/1250000000 : ℝ)|=(271428477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267532701/10000000000 : ℝ)|^8459 ≤ (8584290503527/20000000000000 : ℝ)^6411
        have hw : |(5267532701/10000000000 : ℝ)|=(5267532701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672088357/5000000000 : ℝ)*x 0 + (658441589/1250000000 : ℝ)*x 1 + (-1085713897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672088357/5000000000 : ℝ)^8459 ≤ (43747383011683/100000000000000 : ℝ)^6411 := by
    have hnat : (2672088357 : ℕ)^8459*100000000000000^6411 ≤ 43747383011683^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672088357 5000000000 43747383011683 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658441589/1250000000 : ℝ)^8459 ≤ (42921452635899/100000000000000 : ℝ)^6411 := by
    have hnat : (658441589 : ℕ)^8459*100000000000000^6411 ≤ 42921452635899^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658441589 1250000000 42921452635899 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085713897/5000000000 : ℝ)^8459 ≤ (13331164337741/100000000000000 : ℝ)^6411 := by
    have hnat : (1085713897 : ℕ)^8459*100000000000000^6411 ≤ 13331164337741^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085713897 5000000000 13331164337741 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672088357/5000000000 : ℝ), (658441589/1250000000 : ℝ), (-1085713897/5000000000 : ℝ)] ![(43747383011683/100000000000000 : ℝ), (42921452635899/100000000000000 : ℝ), (13331164337741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672088357/5000000000 : ℝ)|^8459 ≤ (43747383011683/100000000000000 : ℝ)^6411
        have hw : |(2672088357/5000000000 : ℝ)|=(2672088357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658441589/1250000000 : ℝ)|^8459 ≤ (42921452635899/100000000000000 : ℝ)^6411
        have hw : |(658441589/1250000000 : ℝ)|=(658441589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085713897/5000000000 : ℝ)|^8459 ≤ (13331164337741/100000000000000 : ℝ)^6411
        have hw : |(-1085713897/5000000000 : ℝ)|=(1085713897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347492321/10000000000 : ℝ)*x 0 + (1055923783/2500000000 : ℝ)*x 1 + (4474795337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347492321/10000000000 : ℝ)^8459 ≤ (33317612618929/100000000000000 : ℝ)^6411 := by
    have hnat : (4347492321 : ℕ)^8459*100000000000000^6411 ≤ 33317612618929^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347492321 10000000000 33317612618929 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055923783/2500000000 : ℝ)^8459 ≤ (32071531502577/100000000000000 : ℝ)^6411 := by
    have hnat : (1055923783 : ℕ)^8459*100000000000000^6411 ≤ 32071531502577^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055923783 2500000000 32071531502577 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474795337/10000000000 : ℝ)^8459 ≤ (34610855854869/100000000000000 : ℝ)^6411 := by
    have hnat : (4474795337 : ℕ)^8459*100000000000000^6411 ≤ 34610855854869^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474795337 10000000000 34610855854869 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347492321/10000000000 : ℝ), (1055923783/2500000000 : ℝ), (4474795337/10000000000 : ℝ)] ![(33317612618929/100000000000000 : ℝ), (32071531502577/100000000000000 : ℝ), (34610855854869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347492321/10000000000 : ℝ)|^8459 ≤ (33317612618929/100000000000000 : ℝ)^6411
        have hw : |(4347492321/10000000000 : ℝ)|=(4347492321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055923783/2500000000 : ℝ)|^8459 ≤ (32071531502577/100000000000000 : ℝ)^6411
        have hw : |(1055923783/2500000000 : ℝ)|=(1055923783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474795337/10000000000 : ℝ)|^8459 ≤ (34610855854869/100000000000000 : ℝ)^6411
        have hw : |(4474795337/10000000000 : ℝ)|=(4474795337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-131810451/625000000 : ℝ)*x 0 + (5267843121/10000000000 : ℝ)*x 1 + (5390431637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131810451/625000000 : ℝ)^8459 ≤ (6413768818157/50000000000000 : ℝ)^6411 := by
    have hnat : (131810451 : ℕ)^8459*50000000000000^6411 ≤ 6413768818157^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131810451 625000000 6413768818157 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267843121/10000000000 : ℝ)^8459 ≤ (1716991598531/4000000000000 : ℝ)^6411 := by
    have hnat : (5267843121 : ℕ)^8459*4000000000000^6411 ≤ 1716991598531^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267843121 10000000000 1716991598531 4000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390431637/10000000000 : ℝ)^8459 ≤ (44247672391729/100000000000000 : ℝ)^6411 := by
    have hnat : (5390431637 : ℕ)^8459*100000000000000^6411 ≤ 44247672391729^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390431637 10000000000 44247672391729 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131810451/625000000 : ℝ), (5267843121/10000000000 : ℝ), (5390431637/10000000000 : ℝ)] ![(6413768818157/50000000000000 : ℝ), (1716991598531/4000000000000 : ℝ), (44247672391729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131810451/625000000 : ℝ)|^8459 ≤ (6413768818157/50000000000000 : ℝ)^6411
        have hw : |(-131810451/625000000 : ℝ)|=(131810451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267843121/10000000000 : ℝ)|^8459 ≤ (1716991598531/4000000000000 : ℝ)^6411
        have hw : |(5267843121/10000000000 : ℝ)|=(5267843121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390431637/10000000000 : ℝ)|^8459 ≤ (44247672391729/100000000000000 : ℝ)^6411
        have hw : |(5390431637/10000000000 : ℝ)|=(5390431637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312688649/10000000000 : ℝ)*x 0 + (-2048529021/10000000000 : ℝ)*x 1 + (539043121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312688649/10000000000 : ℝ)^8459 ≤ (8681520098661/20000000000000 : ℝ)^6411 := by
    have hnat : (5312688649 : ℕ)^8459*20000000000000^6411 ≤ 8681520098661^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312688649 10000000000 8681520098661 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048529021/10000000000 : ℝ)^8459 ≤ (12344731733369/100000000000000 : ℝ)^6411 := by
    have hnat : (2048529021 : ℕ)^8459*100000000000000^6411 ≤ 12344731733369^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048529021 10000000000 12344731733369 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539043121/1000000000 : ℝ)^8459 ≤ (22123833883491/50000000000000 : ℝ)^6411 := by
    have hnat : (539043121 : ℕ)^8459*50000000000000^6411 ≤ 22123833883491^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539043121 1000000000 22123833883491 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312688649/10000000000 : ℝ), (-2048529021/10000000000 : ℝ), (539043121/1000000000 : ℝ)] ![(8681520098661/20000000000000 : ℝ), (12344731733369/100000000000000 : ℝ), (22123833883491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312688649/10000000000 : ℝ)|^8459 ≤ (8681520098661/20000000000000 : ℝ)^6411
        have hw : |(5312688649/10000000000 : ℝ)|=(5312688649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048529021/10000000000 : ℝ)|^8459 ≤ (12344731733369/100000000000000 : ℝ)^6411
        have hw : |(-2048529021/10000000000 : ℝ)|=(2048529021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539043121/1000000000 : ℝ)|^8459 ≤ (22123833883491/50000000000000 : ℝ)^6411
        have hw : |(539043121/1000000000 : ℝ)|=(539043121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656344417/5000000000 : ℝ)*x 0 + (539043081/1000000000 : ℝ)*x 1 + (-1024264657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656344417/5000000000 : ℝ)^8459 ≤ (10851900621931/25000000000000 : ℝ)^6411 := by
    have hnat : (2656344417 : ℕ)^8459*25000000000000^6411 ≤ 10851900621931^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656344417 5000000000 10851900621931 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539043081/1000000000 : ℝ)^8459 ≤ (22123831717333/50000000000000 : ℝ)^6411 := by
    have hnat : (539043081 : ℕ)^8459*50000000000000^6411 ≤ 22123831717333^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539043081 1000000000 22123831717333 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024264657/5000000000 : ℝ)^8459 ≤ (12344734063071/100000000000000 : ℝ)^6411 := by
    have hnat : (1024264657 : ℕ)^8459*100000000000000^6411 ≤ 12344734063071^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024264657 5000000000 12344734063071 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656344417/5000000000 : ℝ), (539043081/1000000000 : ℝ), (-1024264657/5000000000 : ℝ)] ![(10851900621931/25000000000000 : ℝ), (22123831717333/50000000000000 : ℝ), (12344734063071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656344417/5000000000 : ℝ)|^8459 ≤ (10851900621931/25000000000000 : ℝ)^6411
        have hw : |(2656344417/5000000000 : ℝ)|=(2656344417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539043081/1000000000 : ℝ)|^8459 ≤ (22123831717333/50000000000000 : ℝ)^6411
        have hw : |(539043081/1000000000 : ℝ)|=(539043081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024264657/5000000000 : ℝ)|^8459 ≤ (12344734063071/100000000000000 : ℝ)^6411
        have hw : |(-1024264657/5000000000 : ℝ)|=(1024264657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s7_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173750933/5000000000 : ℝ)*x 0 + (178966453/400000000 : ℝ)*x 1 + (2112165643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173750933/5000000000 : ℝ)^8459 ≤ (4164713642007/12500000000000 : ℝ)^6411 := by
    have hnat : (2173750933 : ℕ)^8459*12500000000000^6411 ≤ 4164713642007^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173750933 5000000000 4164713642007 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178966453/400000000 : ℝ)^8459 ≤ (6920877123961/20000000000000 : ℝ)^6411 := by
    have hnat : (178966453 : ℕ)^8459*20000000000000^6411 ≤ 6920877123961^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178966453 400000000 6920877123961 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112165643/5000000000 : ℝ)^8459 ≤ (6415581044847/20000000000000 : ℝ)^6411 := by
    have hnat : (2112165643 : ℕ)^8459*20000000000000^6411 ≤ 6415581044847^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112165643 5000000000 6415581044847 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173750933/5000000000 : ℝ), (178966453/400000000 : ℝ), (2112165643/5000000000 : ℝ)] ![(4164713642007/12500000000000 : ℝ), (6920877123961/20000000000000 : ℝ), (6415581044847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173750933/5000000000 : ℝ)|^8459 ≤ (4164713642007/12500000000000 : ℝ)^6411
        have hw : |(2173750933/5000000000 : ℝ)|=(2173750933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(178966453/400000000 : ℝ)|^8459 ≤ (6920877123961/20000000000000 : ℝ)^6411
        have hw : |(178966453/400000000 : ℝ)|=(178966453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112165643/5000000000 : ℝ)|^8459 ≤ (6415581044847/20000000000000 : ℝ)^6411
        have hw : |(2112165643/5000000000 : ℝ)|=(2112165643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11507/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11503/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (13220868510630469/100000000000000000000 : ℝ) := by
    have hpowers : (11503/100000 : ℝ)^4229 ≤ (13220868510630469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11503 : ℕ)^4229*100000000000000000000^1024 ≤ 13220868510630469^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11503 100000 13220868510630469 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11503/100000 : ℝ)) (X := (13220868510630469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (1233399981194487/4000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^4229 ≤ (1233399981194487/4000000000000000000 : ℝ)^1024 := by
      have hnat : (14121 : ℕ)^4229*4000000000000000000^1024 ≤ 1233399981194487^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 1233399981194487 4000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (1233399981194487/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013220868510630469/50000000000000000000 : ℝ) ≤ (10000640189789301/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50013220868510630469/50000000000000000000 : ℝ)^1024 ≤ (10000640189789301/10000000000000000 : ℝ)^4229 := by
      have hnat : (50013220868510630469 : ℕ)^1024*10000000000000000^4229 ≤ 10000640189789301^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013220868510630469 50000000000000000000 10000640189789301 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640189789301/10000000000000000 : ℝ)) (X := (50013220868510630469/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011013967010123161/25000000000000000000 : ℝ) ≤ (10001066580268473/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25011013967010123161/25000000000000000000 : ℝ)^1024 ≤ (10001066580268473/10000000000000000 : ℝ)^4229 := by
      have hnat : (25011013967010123161 : ℕ)^1024*10000000000000000^4229 ≤ 10001066580268473^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011013967010123161 25000000000000000000 10001066580268473 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001066580268473/10000000000000000 : ℝ)) (X := (25011013967010123161/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001233399981194487/2000000000000000000 : ℝ) ≤ (2000298594149529/2000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (2001233399981194487/2000000000000000000 : ℝ)^1024 ≤ (2000298594149529/2000000000000000 : ℝ)^4229 := by
      have hnat : (2001233399981194487 : ℕ)^1024*2000000000000000^4229 ≤ 2000298594149529^4229*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001233399981194487 2000000000000000000 2000298594149529 2000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000298594149529/2000000000000000 : ℝ)) (X := (2001233399981194487/2000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13220868510630469/100000000000000000000 : ℝ) ≤ ((1869419034107468499/1870000000000000000 : ℝ)+2*(15228231399/9350000000000 : ℝ)*(11503/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (1869419034107468499/1870000000000000000 : ℝ)+2*(15228231399/9350000000000 : ℝ)*(11503/100000 : ℝ)=(10000640189789301/10000000000000000 : ℝ) by norm_num, show 1+2*(13220868510630469/100000000000000000000 : ℝ)=(50013220868510630469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1233399981194487/4000000000000000000 : ℝ)+(13220868510630469/100000000000000000000 : ℝ) ≤ ((1869419034107468499/1870000000000000000 : ℝ)+(15228231399/9350000000000 : ℝ)*((14121/100000 : ℝ)+(11503/100000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (1869419034107468499/1870000000000000000 : ℝ)+(15228231399/9350000000000 : ℝ)*((14121/100000 : ℝ)+(11503/100000 : ℝ))=(10001066580268473/10000000000000000 : ℝ) by norm_num, show 1+(1233399981194487/4000000000000000000 : ℝ)+(13220868510630469/100000000000000000000 : ℝ)=(25011013967010123161/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1233399981194487/4000000000000000000 : ℝ) ≤ ((1869419034107468499/1870000000000000000 : ℝ)+2*(15228231399/9350000000000 : ℝ)*(14121/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (1869419034107468499/1870000000000000000 : ℝ)+2*(15228231399/9350000000000 : ℝ)*(14121/100000 : ℝ)=(2000298594149529/2000000000000000 : ℝ) by norm_num, show 1+2*(1233399981194487/4000000000000000000 : ℝ)=(2001233399981194487/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1869419034107468499/1870000000000000000 : ℝ)*(X 1 0+X 2 0)+(15228231399/9350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (1869419034107468499/1870000000000000000 : ℝ)) (alpha := (15228231399/9350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1869419034107468499/1870000000000000000 : ℝ)*(X 0 1+X 2 1)+(15228231399/9350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (1869419034107468499/1870000000000000000 : ℝ)) (alpha := (15228231399/9350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1869419034107468499/1870000000000000000 : ℝ)*(X 0 2+X 1 2)+(15228231399/9350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11503/100000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (1869419034107468499/1870000000000000000 : ℝ)) (alpha := (15228231399/9350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108962363/10000000000 : ℝ)*X 0 0+(5390743357/10000000000 : ℝ)*X 0 1+(2633766359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344176709/10000000000 : ℝ)*X 1 0+(-271428477/1250000000 : ℝ)*X 1 1+(5267532701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672088357/5000000000 : ℝ)*X 2 0+(658441589/1250000000 : ℝ)*X 2 1+(-1085713897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347492321/10000000000 : ℝ)*X 0 0+(1055923783/2500000000 : ℝ)*X 0 1+(4474795337/10000000000 : ℝ)*X 0 2+(4347492321/10000000000 : ℝ)*X 1 0+(1055923783/2500000000 : ℝ)*X 1 1+(4474795337/10000000000 : ℝ)*X 1 2+(4347492321/10000000000 : ℝ)*X 2 0+(1055923783/2500000000 : ℝ)*X 2 1+(4474795337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-131810451/625000000 : ℝ)*X 0 0+(5267843121/10000000000 : ℝ)*X 0 1+(5390431637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312688649/10000000000 : ℝ)*X 1 0+(-2048529021/10000000000 : ℝ)*X 1 1+(539043121/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656344417/5000000000 : ℝ)*X 2 0+(539043081/1000000000 : ℝ)*X 2 1+(-1024264657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173750933/5000000000 : ℝ)*X 0 0+(178966453/400000000 : ℝ)*X 0 1+(2112165643/5000000000 : ℝ)*X 0 2+(2173750933/5000000000 : ℝ)*X 1 0+(178966453/400000000 : ℝ)*X 1 1+(2112165643/5000000000 : ℝ)*X 1 2+(2173750933/5000000000 : ℝ)*X 2 0+(178966453/400000000 : ℝ)*X 2 1+(2112165643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (252713316493102483344105381/46750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207649883/20000000000000 : ℝ)*(base19) + (39526793/4000000000000 : ℝ)*(base23) + (963173/3125000000000 : ℝ)*(lower2) + (27779051/25000000000000 : ℝ)*(upper3) + (106172701/100000000000000 : ℝ)*(upper5) + (6049371648734627/100000000000000 : ℝ)*(major0) + (6049371648734627/100000000000000 : ℝ)*(major1) + (6049371648734627/100000000000000 : ℝ)*(major2) + (253631597106331/3125000000000 : ℝ)*(sp0) + (324649595402581/4000000000000 : ℝ)*(sp1) + (1623247987028823/20000000000000 : ℝ)*(sp2) + (3982487747712049/100000000000000 : ℝ)*(sp3) + (7453977837/25000000000000 : ℝ)*(sp4) + (14446255511/100000000000000 : ℝ)*(sp7) + (99562554849189/2500000000000 : ℝ)*(f.failure) + (405812046165697/5000000000000 : ℝ)*(f.sum) + (2781585717239/935000000000000000000000000 : ℝ)*base66 + (732693463182614873/187000000000000000000000000000000 : ℝ)*base67 + (1080218303130614873/187000000000000000000000000000000 : ℝ)*base69 + (1056739875487614873/187000000000000000000000000000000 : ℝ)*base71 + (465200777359/935000000000000000000000000 : ℝ)*base74 + (1953880378339614873/187000000000000000000000000000000 : ℝ)*base75 + (2337308233007385127/187000000000000000000000000000000 : ℝ)*base78 + (1304806606146614873/187000000000000000000000000000000 : ℝ)*base79 + (372701419969/935000000000000000000000000 : ℝ)*base82 + (570317/50000000000000000000 : ℝ)*base89 + (570317/50000000000000000000 : ℝ)*base91 + (570317/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30704963041796856717970281/46750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (821526809/50000000000000 : ℝ)*(base19) + (2054867993/100000000000000 : ℝ)*(base23) + (35199333/25000000000000 : ℝ)*(upper2) + (300721739/100000000000000 : ℝ)*(upper5) + (3040036863674309/50000000000000 : ℝ)*(major0) + (3040036863674309/50000000000000 : ℝ)*(major1) + (3040036863674309/50000000000000 : ℝ)*(major2) + (24757111453/100000000000000 : ℝ)*(sp0) + (7255139889/12500000000000 : ℝ)*(sp1) + (17440770017/50000000000000 : ℝ)*(sp2) + (65259266272579/800000000000 : ℝ)*(sp4) + (8157373357011097/100000000000000 : ℝ)*(sp5) + (40786980523879/500000000000 : ℝ)*(sp6) + (2001357195810189/50000000000000 : ℝ)*(sp7) + (2001357195810189/50000000000000 : ℝ)*(f.failure) + (2039358260295957/25000000000000 : ℝ)*(f.sum) + (2894612858249/935000000000000000000000000 : ℝ)*base65 + (88041293820292191/93500000000000000000000000000000 : ℝ)*base67 + (879438169611792191/93500000000000000000000000000000 : ℝ)*base69 + (530091083479792191/93500000000000000000000000000000 : ℝ)*base71 + (4997527205471/935000000000000000000000000 : ℝ)*base74 + (932408560706292191/93500000000000000000000000000000 : ℝ)*base75 + (282233325227292191/93500000000000000000000000000000 : ℝ)*base77 + (441776093348292191/93500000000000000000000000000000 : ℝ)*base79 + (836000651139/233750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3296683/1000000000000000000000 : ℝ)*base90 + (3296683/1000000000000000000000 : ℝ)*base92 + (3296683/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1266_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s8_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108964913/10000000000 : ℝ)*x 0 + (13476767/25000000 : ℝ)*x 1 + (5267567643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108964913/10000000000 : ℝ)^8459 ≤ (641375957691/5000000000000 : ℝ)^6411 := by
    have hnat : (2108964913 : ℕ)^8459*5000000000000^6411 ≤ 641375957691^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108964913 10000000000 641375957691 5000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13476767/25000000 : ℝ)^8459 ≤ (22125326324349/50000000000000 : ℝ)^6411 := by
    have hnat : (13476767 : ℕ)^8459*50000000000000^6411 ≤ 22125326324349^6411*25000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13476767 25000000 22125326324349 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267567643/10000000000 : ℝ)^8459 ≤ (42921828189471/100000000000000 : ℝ)^6411 := by
    have hnat : (5267567643 : ℕ)^8459*100000000000000^6411 ≤ 42921828189471^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267567643 10000000000 42921828189471 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108964913/10000000000 : ℝ), (13476767/25000000 : ℝ), (5267567643/10000000000 : ℝ)] ![(641375957691/5000000000000 : ℝ), (22125326324349/50000000000000 : ℝ), (42921828189471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108964913/10000000000 : ℝ)|^8459 ≤ (641375957691/5000000000000 : ℝ)^6411
        have hw : |(-2108964913/10000000000 : ℝ)|=(2108964913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13476767/25000000 : ℝ)|^8459 ≤ (22125326324349/50000000000000 : ℝ)^6411
        have hw : |(13476767/25000000 : ℝ)|=(13476767/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267567643/10000000000 : ℝ)|^8459 ≤ (42921828189471/100000000000000 : ℝ)^6411
        have hw : |(5267567643/10000000000 : ℝ)|=(5267567643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344167753/10000000000 : ℝ)*x 0 + (-67856053/312500000 : ℝ)*x 1 + (2633783703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344167753/10000000000 : ℝ)^8459 ≤ (21873643111913/50000000000000 : ℝ)^6411 := by
    have hnat : (5344167753 : ℕ)^8459*50000000000000^6411 ≤ 21873643111913^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344167753 10000000000 21873643111913 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67856053/312500000 : ℝ)^8459 ≤ (1333088812497/10000000000000 : ℝ)^6411 := by
    have hnat : (67856053 : ℕ)^8459*10000000000000^6411 ≤ 1333088812497^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67856053 312500000 1333088812497 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633783703/5000000000 : ℝ)^8459 ≤ (42921825641411/100000000000000 : ℝ)^6411 := by
    have hnat : (2633783703 : ℕ)^8459*100000000000000^6411 ≤ 42921825641411^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633783703 5000000000 42921825641411 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344167753/10000000000 : ℝ), (-67856053/312500000 : ℝ), (2633783703/5000000000 : ℝ)] ![(21873643111913/50000000000000 : ℝ), (1333088812497/10000000000000 : ℝ), (42921825641411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344167753/10000000000 : ℝ)|^8459 ≤ (21873643111913/50000000000000 : ℝ)^6411
        have hw : |(5344167753/10000000000 : ℝ)|=(5344167753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67856053/312500000 : ℝ)|^8459 ≤ (1333088812497/10000000000000 : ℝ)^6411
        have hw : |(-67856053/312500000 : ℝ)|=(67856053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633783703/5000000000 : ℝ)|^8459 ≤ (42921825641411/100000000000000 : ℝ)^6411
        have hw : |(2633783703/5000000000 : ℝ)|=(2633783703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334010517/625000000 : ℝ)*x 0 + (2633783517/5000000000 : ℝ)*x 1 + (-2171393497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334010517/625000000 : ℝ)^8459 ≤ (43747291829549/100000000000000 : ℝ)^6411 := by
    have hnat : (334010517 : ℕ)^8459*100000000000000^6411 ≤ 43747291829549^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334010517 625000000 43747291829549 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633783517/5000000000 : ℝ)^8459 ≤ (10730455410481/25000000000000 : ℝ)^6411 := by
    have hnat : (2633783517 : ℕ)^8459*25000000000000^6411 ≤ 10730455410481^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633783517 5000000000 10730455410481 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171393497/10000000000 : ℝ)^8459 ≤ (3332721628241/25000000000000 : ℝ)^6411 := by
    have hnat : (2171393497 : ℕ)^8459*25000000000000^6411 ≤ 3332721628241^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171393497 10000000000 3332721628241 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334010517/625000000 : ℝ), (2633783517/5000000000 : ℝ), (-2171393497/10000000000 : ℝ)] ![(43747291829549/100000000000000 : ℝ), (10730455410481/25000000000000 : ℝ), (3332721628241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334010517/625000000 : ℝ)|^8459 ≤ (43747291829549/100000000000000 : ℝ)^6411
        have hw : |(334010517/625000000 : ℝ)|=(334010517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633783517/5000000000 : ℝ)|^8459 ≤ (10730455410481/25000000000000 : ℝ)^6411
        have hw : |(2633783517/5000000000 : ℝ)|=(2633783517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171393497/10000000000 : ℝ)|^8459 ≤ (3332721628241/25000000000000 : ℝ)^6411
        have hw : |(-2171393497/10000000000 : ℝ)|=(2171393497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173747021/5000000000 : ℝ)*x 0 + (422376719/1000000000 : ℝ)*x 1 + (1118680723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173747021/5000000000 : ℝ)^8459 ≤ (33317630021331/100000000000000 : ℝ)^6411 := by
    have hnat : (2173747021 : ℕ)^8459*100000000000000^6411 ≤ 33317630021331^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173747021 5000000000 33317630021331 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422376719/1000000000 : ℝ)^8459 ≤ (32072253447009/100000000000000 : ℝ)^6411 := by
    have hnat : (422376719 : ℕ)^8459*100000000000000^6411 ≤ 32072253447009^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422376719 1000000000 32072253447009 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118680723/2500000000 : ℝ)^8459 ≤ (34610116522529/100000000000000 : ℝ)^6411 := by
    have hnat : (1118680723 : ℕ)^8459*100000000000000^6411 ≤ 34610116522529^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118680723 2500000000 34610116522529 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173747021/5000000000 : ℝ), (422376719/1000000000 : ℝ), (1118680723/2500000000 : ℝ)] ![(33317630021331/100000000000000 : ℝ), (32072253447009/100000000000000 : ℝ), (34610116522529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173747021/5000000000 : ℝ)|^8459 ≤ (33317630021331/100000000000000 : ℝ)^6411
        have hw : |(2173747021/5000000000 : ℝ)|=(2173747021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422376719/1000000000 : ℝ)|^8459 ≤ (32072253447009/100000000000000 : ℝ)^6411
        have hw : |(422376719/1000000000 : ℝ)|=(422376719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1118680723/2500000000 : ℝ)|^8459 ≤ (34610116522529/100000000000000 : ℝ)^6411
        have hw : |(1118680723/2500000000 : ℝ)|=(1118680723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108969459/10000000000 : ℝ)*x 0 + (1053575687/2000000000 : ℝ)*x 1 + (5390394919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108969459/10000000000 : ℝ)^8459 ≤ (12827555637291/100000000000000 : ℝ)^6411 := by
    have hnat : (2108969459 : ℕ)^8459*100000000000000^6411 ≤ 12827555637291^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108969459 10000000000 12827555637291 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053575687/2000000000 : ℝ)^8459 ≤ (21462584820873/50000000000000 : ℝ)^6411 := by
    have hnat : (1053575687 : ℕ)^8459*50000000000000^6411 ≤ 21462584820873^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053575687 2000000000 21462584820873 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390394919/10000000000 : ℝ)^8459 ≤ (22123637353607/50000000000000 : ℝ)^6411 := by
    have hnat : (5390394919 : ℕ)^8459*50000000000000^6411 ≤ 22123637353607^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390394919 10000000000 22123637353607 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108969459/10000000000 : ℝ), (1053575687/2000000000 : ℝ), (5390394919/10000000000 : ℝ)] ![(12827555637291/100000000000000 : ℝ), (21462584820873/50000000000000 : ℝ), (22123637353607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108969459/10000000000 : ℝ)|^8459 ≤ (12827555637291/100000000000000 : ℝ)^6411
        have hw : |(-2108969459/10000000000 : ℝ)|=(2108969459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053575687/2000000000 : ℝ)|^8459 ≤ (21462584820873/50000000000000 : ℝ)^6411
        have hw : |(1053575687/2000000000 : ℝ)|=(1053575687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390394919/10000000000 : ℝ)|^8459 ≤ (22123637353607/50000000000000 : ℝ)^6411
        have hw : |(5390394919/10000000000 : ℝ)|=(5390394919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166021787/312500000 : ℝ)*x 0 + (-40971321/200000000 : ℝ)*x 1 + (5390395529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166021787/312500000 : ℝ)^8459 ≤ (10851923126529/25000000000000 : ℝ)^6411 := by
    have hnat : (166021787 : ℕ)^8459*25000000000000^6411 ≤ 10851923126529^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166021787 312500000 10851923126529 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40971321/200000000 : ℝ)^8459 ≤ (493801046371/4000000000000 : ℝ)^6411 := by
    have hnat : (40971321 : ℕ)^8459*4000000000000^6411 ≤ 493801046371^6411*200000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40971321 200000000 493801046371 4000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390395529/10000000000 : ℝ)^8459 ≤ (22123640656991/50000000000000 : ℝ)^6411 := by
    have hnat : (5390395529 : ℕ)^8459*50000000000000^6411 ≤ 22123640656991^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390395529 10000000000 22123640656991 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166021787/312500000 : ℝ), (-40971321/200000000 : ℝ), (5390395529/10000000000 : ℝ)] ![(10851923126529/25000000000000 : ℝ), (493801046371/4000000000000 : ℝ), (22123640656991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166021787/312500000 : ℝ)|^8459 ≤ (10851923126529/25000000000000 : ℝ)^6411
        have hw : |(166021787/312500000 : ℝ)|=(166021787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40971321/200000000 : ℝ)|^8459 ≤ (493801046371/4000000000000 : ℝ)^6411
        have hw : |(-40971321/200000000 : ℝ)|=(40971321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390395529/10000000000 : ℝ)|^8459 ≤ (22123640656991/50000000000000 : ℝ)^6411
        have hw : |(5390395529/10000000000 : ℝ)|=(5390395529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656348713/5000000000 : ℝ)*x 0 + (5390395241/10000000000 : ℝ)*x 1 + (-409713223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656348713/5000000000 : ℝ)^8459 ≤ (43407695115033/100000000000000 : ℝ)^6411 := by
    have hnat : (2656348713 : ℕ)^8459*100000000000000^6411 ≤ 43407695115033^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656348713 5000000000 43407695115033 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390395241/10000000000 : ℝ)^8459 ≤ (44247278194721/100000000000000 : ℝ)^6411 := by
    have hnat : (5390395241 : ℕ)^8459*100000000000000^6411 ≤ 44247278194721^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390395241 10000000000 44247278194721 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409713223/2000000000 : ℝ)^8459 ≤ (12345026676107/100000000000000 : ℝ)^6411 := by
    have hnat : (409713223 : ℕ)^8459*100000000000000^6411 ≤ 12345026676107^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409713223 2000000000 12345026676107 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656348713/5000000000 : ℝ), (5390395241/10000000000 : ℝ), (-409713223/2000000000 : ℝ)] ![(43407695115033/100000000000000 : ℝ), (44247278194721/100000000000000 : ℝ), (12345026676107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656348713/5000000000 : ℝ)|^8459 ≤ (43407695115033/100000000000000 : ℝ)^6411
        have hw : |(2656348713/5000000000 : ℝ)|=(2656348713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390395241/10000000000 : ℝ)|^8459 ≤ (44247278194721/100000000000000 : ℝ)^6411
        have hw : |(5390395241/10000000000 : ℝ)|=(5390395241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409713223/2000000000 : ℝ)|^8459 ≤ (12345026676107/100000000000000 : ℝ)^6411
        have hw : |(-409713223/2000000000 : ℝ)|=(409713223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173751703/5000000000 : ℝ)*x 0 + (2237044909/5000000000 : ℝ)*x 1 + (4224402563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173751703/5000000000 : ℝ)^8459 ≤ (33317724708233/100000000000000 : ℝ)^6411 := by
    have hnat : (2173751703 : ℕ)^8459*100000000000000^6411 ≤ 33317724708233^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173751703 5000000000 33317724708233 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237044909/5000000000 : ℝ)^8459 ≤ (6920731178633/20000000000000 : ℝ)^6411 := by
    have hnat : (2237044909 : ℕ)^8459*20000000000000^6411 ≤ 6920731178633^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237044909 5000000000 6920731178633 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224402563/10000000000 : ℝ)^8459 ≤ (6415723875643/20000000000000 : ℝ)^6411 := by
    have hnat : (4224402563 : ℕ)^8459*20000000000000^6411 ≤ 6415723875643^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224402563 10000000000 6415723875643 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173751703/5000000000 : ℝ), (2237044909/5000000000 : ℝ), (4224402563/10000000000 : ℝ)] ![(33317724708233/100000000000000 : ℝ), (6920731178633/20000000000000 : ℝ), (6415723875643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173751703/5000000000 : ℝ)|^8459 ≤ (33317724708233/100000000000000 : ℝ)^6411
        have hw : |(2173751703/5000000000 : ℝ)|=(2173751703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237044909/5000000000 : ℝ)|^8459 ≤ (6920731178633/20000000000000 : ℝ)^6411
        have hw : |(2237044909/5000000000 : ℝ)|=(2237044909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224402563/10000000000 : ℝ)|^8459 ≤ (6415723875643/20000000000000 : ℝ)^6411
        have hw : |(4224402563/10000000000 : ℝ)|=(4224402563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s8_8 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-44593019/10000000000 : ℝ)*x 0 + (2955022459/5000000000 : ℝ)*x 1 + (2955032609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44593019/10000000000 : ℝ)^8459 ≤ (39563341519/50000000000000 : ℝ)^6411 := by
    have hnat : (44593019 : ℕ)^8459*50000000000000^6411 ≤ 39563341519^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44593019 10000000000 39563341519 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2955022459/5000000000 : ℝ)^8459 ≤ (12490080859971/25000000000000 : ℝ)^6411 := by
    have hnat : (2955022459 : ℕ)^8459*25000000000000^6411 ≤ 12490080859971^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955022459 5000000000 12490080859971 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2955032609/5000000000 : ℝ)^8459 ≤ (49960549864679/100000000000000 : ℝ)^6411 := by
    have hnat : (2955032609 : ℕ)^8459*100000000000000^6411 ≤ 49960549864679^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955032609 5000000000 49960549864679 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44593019/10000000000 : ℝ), (2955022459/5000000000 : ℝ), (2955032609/5000000000 : ℝ)] ![(39563341519/50000000000000 : ℝ), (12490080859971/25000000000000 : ℝ), (49960549864679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44593019/10000000000 : ℝ)|^8459 ≤ (39563341519/50000000000000 : ℝ)^6411
        have hw : |(-44593019/10000000000 : ℝ)|=(44593019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2955022459/5000000000 : ℝ)|^8459 ≤ (12490080859971/25000000000000 : ℝ)^6411
        have hw : |(2955022459/5000000000 : ℝ)|=(2955022459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2955032609/5000000000 : ℝ)|^8459 ≤ (49960549864679/100000000000000 : ℝ)^6411
        have hw : |(2955032609/5000000000 : ℝ)|=(2955032609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2877/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11507/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (13239865418511541/100000000000000000000 : ℝ) := by
    have hpowers : (11507/100000 : ℝ)^4229 ≤ (13239865418511541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11507 : ℕ)^4229*100000000000000000000^1024 ≤ 13239865418511541^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11507 100000 13239865418511541 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11507/100000 : ℝ)) (X := (13239865418511541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (30798943019816531/100000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^4229 ≤ (30798943019816531/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14117 : ℕ)^4229*100000000000000000000^1024 ≤ 30798943019816531^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 30798943019816531 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (30798943019816531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013239865418511541/50000000000000000000 : ℝ) ≤ (10000641109578073/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50013239865418511541/50000000000000000000 : ℝ)^1024 ≤ (10000641109578073/10000000000000000 : ℝ)^4229 := by
      have hnat : (50013239865418511541 : ℕ)^1024*10000000000000000^4229 ≤ 10000641109578073^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013239865418511541 50000000000000000000 10000641109578073 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641109578073/10000000000000000 : ℝ)) (X := (50013239865418511541/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505504851054791009/12500000000000000000 : ℝ) ≤ (10001066167329163/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (12505504851054791009/12500000000000000000 : ℝ)^1024 ≤ (10001066167329163/10000000000000000 : ℝ)^4229 := by
      have hnat : (12505504851054791009 : ℕ)^1024*10000000000000000^4229 ≤ 10001066167329163^4229*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505504851054791009 12500000000000000000 10001066167329163 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001066167329163/10000000000000000 : ℝ)) (X := (12505504851054791009/12500000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030798943019816531/50000000000000000000 : ℝ) ≤ (10001491225080253/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50030798943019816531/50000000000000000000 : ℝ)^1024 ≤ (10001491225080253/10000000000000000 : ℝ)^4229 := by
      have hnat : (50030798943019816531 : ℕ)^1024*10000000000000000^4229 ≤ 10001491225080253^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030798943019816531 50000000000000000000 10001491225080253 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001491225080253/10000000000000000 : ℝ)) (X := (50030798943019816531/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13239865418511541/100000000000000000000 : ℝ) ≤ ((289909900187946503/290000000000000000 : ℝ)+2*(4722863901/2900000000000 : ℝ)*(11507/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (289909900187946503/290000000000000000 : ℝ)+2*(4722863901/2900000000000 : ℝ)*(11507/100000 : ℝ)=(10000641109578073/10000000000000000 : ℝ) by norm_num, show 1+2*(13239865418511541/100000000000000000000 : ℝ)=(50013239865418511541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30798943019816531/100000000000000000000 : ℝ)+(13239865418511541/100000000000000000000 : ℝ) ≤ ((289909900187946503/290000000000000000 : ℝ)+(4722863901/2900000000000 : ℝ)*((14117/100000 : ℝ)+(11507/100000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (289909900187946503/290000000000000000 : ℝ)+(4722863901/2900000000000 : ℝ)*((14117/100000 : ℝ)+(11507/100000 : ℝ))=(10001066167329163/10000000000000000 : ℝ) by norm_num, show 1+(30798943019816531/100000000000000000000 : ℝ)+(13239865418511541/100000000000000000000 : ℝ)=(12505504851054791009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30798943019816531/100000000000000000000 : ℝ) ≤ ((289909900187946503/290000000000000000 : ℝ)+2*(4722863901/2900000000000 : ℝ)*(14117/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (289909900187946503/290000000000000000 : ℝ)+2*(4722863901/2900000000000 : ℝ)*(14117/100000 : ℝ)=(10001491225080253/10000000000000000 : ℝ) by norm_num, show 1+2*(30798943019816531/100000000000000000000 : ℝ)=(50030798943019816531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (289909900187946503/290000000000000000 : ℝ)*(X 1 0+X 2 0)+(4722863901/2900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (289909900187946503/290000000000000000 : ℝ)) (alpha := (4722863901/2900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (289909900187946503/290000000000000000 : ℝ)*(X 0 1+X 2 1)+(4722863901/2900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (289909900187946503/290000000000000000 : ℝ)) (alpha := (4722863901/2900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (289909900187946503/290000000000000000 : ℝ)*(X 0 2+X 1 2)+(4722863901/2900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (289909900187946503/290000000000000000 : ℝ)) (alpha := (4722863901/2900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108964913/10000000000 : ℝ)*X 0 0+(13476767/25000000 : ℝ)*X 0 1+(5267567643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344167753/10000000000 : ℝ)*X 1 0+(-67856053/312500000 : ℝ)*X 1 1+(2633783703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334010517/625000000 : ℝ)*X 2 0+(2633783517/5000000000 : ℝ)*X 2 1+(-2171393497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173747021/5000000000 : ℝ)*X 0 0+(422376719/1000000000 : ℝ)*X 0 1+(1118680723/2500000000 : ℝ)*X 0 2+(2173747021/5000000000 : ℝ)*X 1 0+(422376719/1000000000 : ℝ)*X 1 1+(1118680723/2500000000 : ℝ)*X 1 2+(2173747021/5000000000 : ℝ)*X 2 0+(422376719/1000000000 : ℝ)*X 2 1+(1118680723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108969459/10000000000 : ℝ)*X 0 0+(1053575687/2000000000 : ℝ)*X 0 1+(5390394919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((166021787/312500000 : ℝ)*X 1 0+(-40971321/200000000 : ℝ)*X 1 1+(5390395529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656348713/5000000000 : ℝ)*X 2 0+(5390395241/10000000000 : ℝ)*X 2 1+(-409713223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173751703/5000000000 : ℝ)*X 0 0+(2237044909/5000000000 : ℝ)*X 0 1+(4224402563/10000000000 : ℝ)*X 0 2+(2173751703/5000000000 : ℝ)*X 1 0+(2237044909/5000000000 : ℝ)*X 1 1+(4224402563/10000000000 : ℝ)*X 1 2+(2173751703/5000000000 : ℝ)*X 2 0+(2237044909/5000000000 : ℝ)*X 2 1+(4224402563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-44593019/10000000000 : ℝ)*X 0 0+(2955022459/5000000000 : ℝ)*X 0 1+(2955032609/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s8_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1445333890599507736458033/453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349564749/50000000000000 : ℝ)*(lower2) + (31735553/6250000000000 : ℝ)*(lower3) + (325304649/100000000000000 : ℝ)*(lower4) + (197624049/100000000000000 : ℝ)*(lower5) + (94575270812519/1562500000000 : ℝ)*(major0) + (94575270812519/1562500000000 : ℝ)*(major1) + (94575270812519/1562500000000 : ℝ)*(major2) + (1624171809708323/20000000000000 : ℝ)*(sp0) + (507553997251327/6250000000000 : ℝ)*(sp1) + (253776525489477/3125000000000 : ℝ)*(sp2) + (199238402456759/5000000000000 : ℝ)*(sp3) + (15140357967/100000000000000 : ℝ)*(sp6) + (1276261293/50000000000000 : ℝ)*(sp7) + (4907479617/100000000000000 : ℝ)*(sp8) + (3984770601657767/100000000000000 : ℝ)*(f.failure) + (507553997251327/6250000000000 : ℝ)*(f.sum) + (1007656900603/72500000000000000000000000 : ℝ)*base65 + (4974937534914807/453125000000000000000000000000 : ℝ)*base67 + (2385640196368071/56640625000000000000000000000 : ℝ)*base70 + (19372637670508557/453125000000000000000000000000 : ℝ)*base71 + (69582851851/36250000000000000000000000 : ℝ)*base74 + (5101022164522693/453125000000000000000000000000 : ℝ)*base76 + (8558120317914807/453125000000000000000000000000 : ℝ)*base77 + (4766335072980841/226562500000000000000000000000 : ℝ)*base79 + (686510175809/145000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31991551/2000000000000000000000 : ℝ)*base89 + (31991551/2000000000000000000000 : ℝ)*base91 + (31991551/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22828925053514438405193999/7250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173014107/100000000000000 : ℝ)*(base15) + (34806887/12500000000000 : ℝ)*(lower1) + (14231751/20000000000000 : ℝ)*(lower2) + (3626463/12500000000000 : ℝ)*(upper3) + (10186783/50000000000000 : ℝ)*(upper4) + (6083586200243389/100000000000000 : ℝ)*(major0) + (6083586200243389/100000000000000 : ℝ)*(major1) + (6083586200243389/100000000000000 : ℝ)*(major2) + (494403389/6250000000000 : ℝ)*(sp1) + (13079120987/100000000000000 : ℝ)*(sp3) + (2040536381596491/25000000000000 : ℝ)*(sp4) + (4081068721458817/50000000000000 : ℝ)*(sp5) + (2040536381596491/25000000000000 : ℝ)*(sp6) + (1001253422504807/25000000000000 : ℝ)*(sp7) + (500628346142527/12500000000000 : ℝ)*(f.failure) + (2040536381596491/25000000000000 : ℝ)*(f.sum) + (244354901319/145000000000000000000000000 : ℝ)*base65 + (336831424914318667/29000000000000000000000000000000 : ℝ)*base67 + (2527163454924318667/29000000000000000000000000000000 : ℝ)*base69 + (366306389681333/29000000000000000000000000000000 : ℝ)*base72 + (32343216861/145000000000000000000000000 : ℝ)*base74 + (692978286918318667/29000000000000000000000000000000 : ℝ)*base75 + (125895420866318667/29000000000000000000000000000000 : ℝ)*base77 + (422888606378318667/29000000000000000000000000000000 : ℝ)*base79 + (9380206143829/145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (555831/250000000000000000000 : ℝ)*base89 + (555831/250000000000000000000 : ℝ)*base91 + (555831/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1266_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1266_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (707/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1266_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1266_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1266_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (707/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2877/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
