-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1313_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:02.261117+00:00
-- url     : https://prove2.me/submissions/72439dc7-d4e7-4def-bd0b-8355bdb30803

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
theorem support_rectangle_w1313_s3_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033604443/5000000000 : ℝ)*x 0 + (5431049991/10000000000 : ℝ)*x 1 + (522819257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033604443/5000000000 : ℝ)^4273 ≤ (12577993997047/100000000000000 : ℝ)^3249 := by
    have hnat : (1033604443 : ℕ)^4273*100000000000000^3249 ≤ 12577993997047^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033604443 5000000000 12577993997047 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431049991/10000000000 : ℝ)^4273 ≤ (560061999869/1250000000000 : ℝ)^3249 := by
    have hnat : (5431049991 : ℕ)^4273*1250000000000^3249 ≤ 560061999869^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431049991 10000000000 560061999869 1250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522819257/1000000000 : ℝ)^4273 ≤ (42617046000433/100000000000000 : ℝ)^3249 := by
    have hnat : (522819257 : ℕ)^4273*100000000000000^3249 ≤ 42617046000433^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522819257 1000000000 42617046000433 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033604443/5000000000 : ℝ), (5431049991/10000000000 : ℝ), (522819257/1000000000 : ℝ)] ![(12577993997047/100000000000000 : ℝ), (560061999869/1250000000000 : ℝ), (42617046000433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033604443/5000000000 : ℝ)|^4273 ≤ (12577993997047/100000000000000 : ℝ)^3249
        have hw : |(-1033604443/5000000000 : ℝ)|=(1033604443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431049991/10000000000 : ℝ)|^4273 ≤ (560061999869/1250000000000 : ℝ)^3249
        have hw : |(5431049991/10000000000 : ℝ)|=(5431049991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522819257/1000000000 : ℝ)|^4273 ≤ (42617046000433/100000000000000 : ℝ)^3249
        have hw : |(522819257/1000000000 : ℝ)|=(522819257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669219201/1250000000 : ℝ)*x 0 + (-434192953/2000000000 : ℝ)*x 1 + (522819259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669219201/1250000000 : ℝ)^4273 ≤ (879363791553/2000000000000 : ℝ)^3249 := by
    have hnat : (669219201 : ℕ)^4273*2000000000000^3249 ≤ 879363791553^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669219201 1250000000 879363791553 2000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434192953/2000000000 : ℝ)^4273 ≤ (13414764196553/100000000000000 : ℝ)^3249 := by
    have hnat : (434192953 : ℕ)^4273*100000000000000^3249 ≤ 13414764196553^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434192953 2000000000 13414764196553 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522819259/1000000000 : ℝ)^4273 ≤ (42617046214843/100000000000000 : ℝ)^3249 := by
    have hnat : (522819259 : ℕ)^4273*100000000000000^3249 ≤ 42617046214843^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522819259 1000000000 42617046214843 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669219201/1250000000 : ℝ), (-434192953/2000000000 : ℝ), (522819259/1000000000 : ℝ)] ![(879363791553/2000000000000 : ℝ), (13414764196553/100000000000000 : ℝ), (42617046214843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669219201/1250000000 : ℝ)|^4273 ≤ (879363791553/2000000000000 : ℝ)^3249
        have hw : |(669219201/1250000000 : ℝ)|=(669219201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434192953/2000000000 : ℝ)|^4273 ≤ (13414764196553/100000000000000 : ℝ)^3249
        have hw : |(-434192953/2000000000 : ℝ)|=(434192953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522819259/1000000000 : ℝ)|^4273 ≤ (42617046214843/100000000000000 : ℝ)^3249
        have hw : |(522819259/1000000000 : ℝ)|=(522819259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353753683/10000000000 : ℝ)*x 0 + (326762021/625000000 : ℝ)*x 1 + (-2170965001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353753683/10000000000 : ℝ)^4273 ≤ (10992047596931/25000000000000 : ℝ)^3249 := by
    have hnat : (5353753683 : ℕ)^4273*25000000000000^3249 ≤ 10992047596931^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353753683 10000000000 10992047596931 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326762021/625000000 : ℝ)^4273 ≤ (42617043491837/100000000000000 : ℝ)^3249 := by
    have hnat : (326762021 : ℕ)^4273*100000000000000^3249 ≤ 42617043491837^3249*625000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326762021 625000000 42617043491837 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170965001/10000000000 : ℝ)^4273 ≤ (13414766114451/100000000000000 : ℝ)^3249 := by
    have hnat : (2170965001 : ℕ)^4273*100000000000000^3249 ≤ 13414766114451^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170965001 10000000000 13414766114451 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353753683/10000000000 : ℝ), (326762021/625000000 : ℝ), (-2170965001/10000000000 : ℝ)] ![(10992047596931/25000000000000 : ℝ), (42617043491837/100000000000000 : ℝ), (13414766114451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353753683/10000000000 : ℝ)|^4273 ≤ (10992047596931/25000000000000 : ℝ)^3249
        have hw : |(5353753683/10000000000 : ℝ)|=(5353753683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326762021/625000000 : ℝ)|^4273 ≤ (42617043491837/100000000000000 : ℝ)^3249
        have hw : |(326762021/625000000 : ℝ)|=(326762021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170965001/10000000000 : ℝ)|^4273 ≤ (13414766114451/100000000000000 : ℝ)^3249
        have hw : |(-2170965001/10000000000 : ℝ)|=(2170965001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083250659/2500000000 : ℝ)*x 0 + (4127689517/10000000000 : ℝ)*x 1 + (4547957933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083250659/2500000000 : ℝ)^4273 ≤ (16645019779373/50000000000000 : ℝ)^3249 := by
    have hnat : (1083250659 : ℕ)^4273*50000000000000^3249 ≤ 16645019779373^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083250659 2500000000 16645019779373 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127689517/10000000000 : ℝ)^4273 ≤ (6246228990903/20000000000000 : ℝ)^3249 := by
    have hnat : (4127689517 : ℕ)^4273*20000000000000^3249 ≤ 6246228990903^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127689517 10000000000 6246228990903 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547957933/10000000000 : ℝ)^4273 ≤ (35478815470469/100000000000000 : ℝ)^3249 := by
    have hnat : (4547957933 : ℕ)^4273*100000000000000^3249 ≤ 35478815470469^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547957933 10000000000 35478815470469 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083250659/2500000000 : ℝ), (4127689517/10000000000 : ℝ), (4547957933/10000000000 : ℝ)] ![(16645019779373/50000000000000 : ℝ), (6246228990903/20000000000000 : ℝ), (35478815470469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083250659/2500000000 : ℝ)|^4273 ≤ (16645019779373/50000000000000 : ℝ)^3249
        have hw : |(1083250659/2500000000 : ℝ)|=(1083250659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127689517/10000000000 : ℝ)|^4273 ≤ (6246228990903/20000000000000 : ℝ)^3249
        have hw : |(4127689517/10000000000 : ℝ)|=(4127689517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547957933/10000000000 : ℝ)|^4273 ≤ (35478815470469/100000000000000 : ℝ)^3249
        have hw : |(4547957933/10000000000 : ℝ)|=(4547957933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067229981/10000000000 : ℝ)*x 0 + (5229053421/10000000000 : ℝ)*x 1 + (1357545951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067229981/10000000000 : ℝ)^4273 ≤ (6289081402019/50000000000000 : ℝ)^3249 := by
    have hnat : (2067229981 : ℕ)^4273*50000000000000^3249 ≤ 6289081402019^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067229981 10000000000 6289081402019 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229053421/10000000000 : ℝ)^4273 ≤ (42626274991079/100000000000000 : ℝ)^3249 := by
    have hnat : (5229053421 : ℕ)^4273*100000000000000^3249 ≤ 42626274991079^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229053421 10000000000 42626274991079 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357545951/2500000000 : ℝ)^4273 ≤ (44795562189037/100000000000000 : ℝ)^3249 := by
    have hnat : (1357545951 : ℕ)^4273*100000000000000^3249 ≤ 44795562189037^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357545951 2500000000 44795562189037 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067229981/10000000000 : ℝ), (5229053421/10000000000 : ℝ), (1357545951/2500000000 : ℝ)] ![(6289081402019/50000000000000 : ℝ), (42626274991079/100000000000000 : ℝ), (44795562189037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067229981/10000000000 : ℝ)|^4273 ≤ (6289081402019/50000000000000 : ℝ)^3249
        have hw : |(-2067229981/10000000000 : ℝ)|=(2067229981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229053421/10000000000 : ℝ)|^4273 ≤ (42626274991079/100000000000000 : ℝ)^3249
        have hw : |(5229053421/10000000000 : ℝ)|=(5229053421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357545951/2500000000 : ℝ)|^4273 ≤ (44795562189037/100000000000000 : ℝ)^3249
        have hw : |(1357545951/2500000000 : ℝ)|=(1357545951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301678621/10000000000 : ℝ)*x 0 + (-492243387/2500000000 : ℝ)*x 1 + (5430183767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301678621/10000000000 : ℝ)^4273 ≤ (542582405867/1250000000000 : ℝ)^3249 := by
    have hnat : (5301678621 : ℕ)^4273*1250000000000^3249 ≤ 542582405867^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301678621 10000000000 542582405867 1250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492243387/2500000000 : ℝ)^4273 ≤ (11797845729653/100000000000000 : ℝ)^3249 := by
    have hnat : (492243387 : ℕ)^4273*100000000000000^3249 ≤ 11797845729653^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492243387 2500000000 11797845729653 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430183767/10000000000 : ℝ)^4273 ≤ (11198890446903/25000000000000 : ℝ)^3249 := by
    have hnat : (5430183767 : ℕ)^4273*25000000000000^3249 ≤ 11198890446903^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430183767 10000000000 11198890446903 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301678621/10000000000 : ℝ), (-492243387/2500000000 : ℝ), (5430183767/10000000000 : ℝ)] ![(542582405867/1250000000000 : ℝ), (11797845729653/100000000000000 : ℝ), (11198890446903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301678621/10000000000 : ℝ)|^4273 ≤ (542582405867/1250000000000 : ℝ)^3249
        have hw : |(5301678621/10000000000 : ℝ)|=(5301678621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492243387/2500000000 : ℝ)|^4273 ≤ (11797845729653/100000000000000 : ℝ)^3249
        have hw : |(-492243387/2500000000 : ℝ)|=(492243387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430183767/10000000000 : ℝ)|^4273 ≤ (11198890446903/25000000000000 : ℝ)^3249
        have hw : |(5430183767/10000000000 : ℝ)|=(5430183767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650839379/5000000000 : ℝ)*x 0 + (135754591/250000000 : ℝ)*x 1 + (-393794707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650839379/5000000000 : ℝ)^4273 ≤ (1356456060767/3125000000000 : ℝ)^3249 := by
    have hnat : (2650839379 : ℕ)^4273*3125000000000^3249 ≤ 1356456060767^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650839379 5000000000 1356456060767 3125000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135754591/250000000 : ℝ)^4273 ≤ (2799722525609/6250000000000 : ℝ)^3249 := by
    have hnat : (135754591 : ℕ)^4273*6250000000000^3249 ≤ 2799722525609^3249*250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135754591 250000000 2799722525609 6250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393794707/2000000000 : ℝ)^4273 ≤ (1474730703401/12500000000000 : ℝ)^3249 := by
    have hnat : (393794707 : ℕ)^4273*12500000000000^3249 ≤ 1474730703401^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393794707 2000000000 1474730703401 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650839379/5000000000 : ℝ), (135754591/250000000 : ℝ), (-393794707/2000000000 : ℝ)] ![(1356456060767/3125000000000 : ℝ), (2799722525609/6250000000000 : ℝ), (1474730703401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650839379/5000000000 : ℝ)|^4273 ≤ (1356456060767/3125000000000 : ℝ)^3249
        have hw : |(2650839379/5000000000 : ℝ)|=(2650839379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135754591/250000000 : ℝ)|^4273 ≤ (2799722525609/6250000000000 : ℝ)^3249
        have hw : |(135754591/250000000 : ℝ)|=(135754591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393794707/2000000000 : ℝ)|^4273 ≤ (1474730703401/12500000000000 : ℝ)^3249
        have hw : |(-393794707/2000000000 : ℝ)|=(393794707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s3_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2166523019/5000000000 : ℝ)*x 0 + (4546174277/10000000000 : ℝ)*x 1 + (2064742107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166523019/5000000000 : ℝ)^4273 ≤ (33290478108597/100000000000000 : ℝ)^3249 := by
    have hnat : (2166523019 : ℕ)^4273*100000000000000^3249 ≤ 33290478108597^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166523019 5000000000 33290478108597 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4546174277/10000000000 : ℝ)^4273 ≤ (35460516775869/100000000000000 : ℝ)^3249 := by
    have hnat : (4546174277 : ℕ)^4273*100000000000000^3249 ≤ 35460516775869^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546174277 10000000000 35460516775869 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064742107/5000000000 : ℝ)^4273 ≤ (31249005098467/100000000000000 : ℝ)^3249 := by
    have hnat : (2064742107 : ℕ)^4273*100000000000000^3249 ≤ 31249005098467^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064742107 5000000000 31249005098467 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166523019/5000000000 : ℝ), (4546174277/10000000000 : ℝ), (2064742107/5000000000 : ℝ)] ![(33290478108597/100000000000000 : ℝ), (35460516775869/100000000000000 : ℝ), (31249005098467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166523019/5000000000 : ℝ)|^4273 ≤ (33290478108597/100000000000000 : ℝ)^3249
        have hw : |(2166523019/5000000000 : ℝ)|=(2166523019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4546174277/10000000000 : ℝ)|^4273 ≤ (35460516775869/100000000000000 : ℝ)^3249
        have hw : |(4546174277/10000000000 : ℝ)|=(4546174277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064742107/5000000000 : ℝ)|^4273 ≤ (31249005098467/100000000000000 : ℝ)^3249
        have hw : |(2064742107/5000000000 : ℝ)|=(2064742107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1931/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2687/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (94/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (507/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1931/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (507/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1931/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (507/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1931/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (507/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1931/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (507/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1931/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (507/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1931/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1931/20000 : ℝ) ^ (267/64 : ℝ) ≤ (726814232805971/12500000000000000000 : ℝ) := by
    have hpowers : (1931/20000 : ℝ)^267 ≤ (726814232805971/12500000000000000000 : ℝ)^64 := by
      have hnat : (1931 : ℕ)^267*12500000000000000000^64 ≤ 726814232805971^64*20000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1931 20000 726814232805971 12500000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1931/20000 : ℝ)) (X := (726814232805971/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (507/3125 : ℝ) ^ (267/64 : ℝ) ≤ (25342394691050807/50000000000000000000 : ℝ) := by
    have hpowers : (507/3125 : ℝ)^267 ≤ (25342394691050807/50000000000000000000 : ℝ)^64 := by
      have hnat : (507 : ℕ)^267*50000000000000000000^64 ≤ 25342394691050807^64*3125^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        507 3125 25342394691050807 50000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (507/3125 : ℝ)) (X := (25342394691050807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250726814232805971/6250000000000000000 : ℝ) ≤ (16000445977453/16000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (6250726814232805971/6250000000000000000 : ℝ)^64 ≤ (16000445977453/16000000000000 : ℝ)^267 := by
      have hnat : (6250726814232805971 : ℕ)^64*16000000000000^267 ≤ 16000445977453^267*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250726814232805971 6250000000000000000 16000445977453 16000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000445977453/16000000000000 : ℝ)) (X := (6250726814232805971/6250000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028249651622274691/50000000000000000000 : ℝ) ≤ (10001353999634047/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (50028249651622274691/50000000000000000000 : ℝ)^64 ≤ (10001353999634047/10000000000000000 : ℝ)^267 := by
      have hnat : (50028249651622274691 : ℕ)^64*10000000000000000^267 ≤ 10001353999634047^267*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028249651622274691 50000000000000000000 10001353999634047 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001353999634047/10000000000000000 : ℝ)) (X := (50028249651622274691/50000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025342394691050807/25000000000000000000 : ℝ) ≤ (10002429263359969/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (25025342394691050807/25000000000000000000 : ℝ)^64 ≤ (10002429263359969/10000000000000000 : ℝ)^267 := by
      have hnat : (25025342394691050807 : ℕ)^64*10000000000000000^267 ≤ 10002429263359969^267*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025342394691050807 25000000000000000000 10002429263359969 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002429263359969/10000000000000000 : ℝ)) (X := (25025342394691050807/25000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(726814232805971/12500000000000000000 : ℝ) ≤ ((13134213534726583861/13138000000000000000 : ℝ)+2*(537631862961/328450000000000 : ℝ)*(1931/20000 : ℝ))^(267/64 : ℝ) := by
    rw [show (13134213534726583861/13138000000000000000 : ℝ)+2*(537631862961/328450000000000 : ℝ)*(1931/20000 : ℝ)=(16000445977453/16000000000000 : ℝ) by norm_num, show 1+2*(726814232805971/12500000000000000000 : ℝ)=(6250726814232805971/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25342394691050807/50000000000000000000 : ℝ)+(726814232805971/12500000000000000000 : ℝ) ≤ ((13134213534726583861/13138000000000000000 : ℝ)+(537631862961/328450000000000 : ℝ)*((507/3125 : ℝ)+(1931/20000 : ℝ)))^(267/64 : ℝ) := by
    rw [show (13134213534726583861/13138000000000000000 : ℝ)+(537631862961/328450000000000 : ℝ)*((507/3125 : ℝ)+(1931/20000 : ℝ))=(10001353999634047/10000000000000000 : ℝ) by norm_num, show 1+(25342394691050807/50000000000000000000 : ℝ)+(726814232805971/12500000000000000000 : ℝ)=(50028249651622274691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25342394691050807/50000000000000000000 : ℝ) ≤ ((13134213534726583861/13138000000000000000 : ℝ)+2*(537631862961/328450000000000 : ℝ)*(507/3125 : ℝ))^(267/64 : ℝ) := by
    rw [show (13134213534726583861/13138000000000000000 : ℝ)+2*(537631862961/328450000000000 : ℝ)*(507/3125 : ℝ)=(10002429263359969/10000000000000000 : ℝ) by norm_num, show 1+2*(25342394691050807/50000000000000000000 : ℝ)=(25025342394691050807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13134213534726583861/13138000000000000000 : ℝ)*(X 1 0+X 2 0)+(537631862961/328450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (1931/20000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (13134213534726583861/13138000000000000000 : ℝ)) (alpha := (537631862961/328450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13134213534726583861/13138000000000000000 : ℝ)*(X 0 1+X 2 1)+(537631862961/328450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (1931/20000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (13134213534726583861/13138000000000000000 : ℝ)) (alpha := (537631862961/328450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13134213534726583861/13138000000000000000 : ℝ)*(X 0 2+X 1 2)+(537631862961/328450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (1931/20000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (13134213534726583861/13138000000000000000 : ℝ)) (alpha := (537631862961/328450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033604443/5000000000 : ℝ)*X 0 0+(5431049991/10000000000 : ℝ)*X 0 1+(522819257/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669219201/1250000000 : ℝ)*X 1 0+(-434192953/2000000000 : ℝ)*X 1 1+(522819259/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353753683/10000000000 : ℝ)*X 2 0+(326762021/625000000 : ℝ)*X 2 1+(-2170965001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083250659/2500000000 : ℝ)*X 0 0+(4127689517/10000000000 : ℝ)*X 0 1+(4547957933/10000000000 : ℝ)*X 0 2+(1083250659/2500000000 : ℝ)*X 1 0+(4127689517/10000000000 : ℝ)*X 1 1+(4547957933/10000000000 : ℝ)*X 1 2+(1083250659/2500000000 : ℝ)*X 2 0+(4127689517/10000000000 : ℝ)*X 2 1+(4547957933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2067229981/10000000000 : ℝ)*X 0 0+(5229053421/10000000000 : ℝ)*X 0 1+(1357545951/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301678621/10000000000 : ℝ)*X 1 0+(-492243387/2500000000 : ℝ)*X 1 1+(5430183767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650839379/5000000000 : ℝ)*X 2 0+(135754591/250000000 : ℝ)*X 2 1+(-393794707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166523019/5000000000 : ℝ)*X 0 0+(4546174277/10000000000 : ℝ)*X 0 1+(2064742107/5000000000 : ℝ)*X 0 2+(2166523019/5000000000 : ℝ)*X 1 0+(4546174277/10000000000 : ℝ)*X 1 1+(2064742107/5000000000 : ℝ)*X 1 2+(2166523019/5000000000 : ℝ)*X 2 0+(4546174277/10000000000 : ℝ)*X 2 1+(2064742107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (716147058409274171621242791/82112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235471443/12500000000000 : ℝ)*(base19) + (54336929/3125000000000 : ℝ)*(base23) + (114596191/100000000000000 : ℝ)*(lower2) + (25161883/6250000000000 : ℝ)*(upper3) + (1827263/25000000000000 : ℝ)*(upper5) + (456818340782459/12500000000000 : ℝ)*(major0) + (456818340782459/12500000000000 : ℝ)*(major1) + (456818340782459/12500000000000 : ℝ)*(major2) + (4929605453950383/100000000000000 : ℝ)*(sp0) + (4929628629119507/100000000000000 : ℝ)*(sp1) + (1232407193527331/25000000000000 : ℝ)*(sp2) + (18589407513171/781250000000 : ℝ)*(sp3) + (25058940669/100000000000000 : ℝ)*(sp4) + (4621806139/25000000000000 : ℝ)*(sp7) + (594865662227611/25000000000000 : ℝ)*(f.failure) + (1232407628222763/25000000000000 : ℝ)*(f.sum) + (103030977177279/32845000000000000000000000000 : ℝ)*base65 + (3236581556369495801/164225000000000000000000000000000 : ℝ)*base68 + (1884899835397395801/164225000000000000000000000000000 : ℝ)*base70 + (229586307821945801/164225000000000000000000000000000 : ℝ)*base72 + (211650463987201/32845000000000000000000000000 : ℝ)*base74 + (73805833850795801/164225000000000000000000000000000 : ℝ)*base76 + (877488261759045801/164225000000000000000000000000000 : ℝ)*base78 + (2018995344711445801/164225000000000000000000000000000 : ℝ)*base80 + (23548594055999/8211250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1215683/125000000000000000000 : ℝ)*base89 + (1215683/125000000000000000000 : ℝ)*base91 + (1215683/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27734719424561841350547/6569000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112714649/10000000000000 : ℝ)*(base19) + (257580173/20000000000000 : ℝ)*(base23) + (57239469/50000000000000 : ℝ)*(upper3) + (18727/160000000000 : ℝ)*(lower4) + (120869029/100000000000000 : ℝ)*(upper5) + (368588286950637/10000000000000 : ℝ)*(major0) + (368588286950637/10000000000000 : ℝ)*(major1) + (368588286950637/10000000000000 : ℝ)*(major2) + (18922126733/100000000000000 : ℝ)*(sp1) + (4990135139/25000000000000 : ℝ)*(sp2) + (4971900095606521/100000000000000 : ℝ)*(sp4) + (2485940023166649/50000000000000 : ℝ)*(sp5) + (49718788471651/1000000000000 : ℝ)*(sp6) + (599966375667711/25000000000000 : ℝ)*(sp7) + (599966375667711/25000000000000 : ℝ)*(f.failure) + (4971900095606521/100000000000000 : ℝ)*(f.sum) + (17185560874871/6569000000000000000000000000 : ℝ)*base66 + (152813872606129457/131380000000000000000000000000000 : ℝ)*base67 + (1943420291655850543/131380000000000000000000000000000 : ℝ)*base70 + (178183000478429457/131380000000000000000000000000000 : ℝ)*base71 + (10665866264863/6569000000000000000000000000 : ℝ)*base74 + (1062083332105610543/131380000000000000000000000000000 : ℝ)*base76 + (119496335481450543/131380000000000000000000000000000 : ℝ)*base78 + (416837160280629457/131380000000000000000000000000000 : ℝ)*base79 + (9093956874253/1642250000000000000000000000 : ℝ)*base82 + (970983/125000000000000000000 : ℝ)*base89 + (970983/125000000000000000000 : ℝ)*base91 + (970983/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1313_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1931/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (94/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1313_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1313_s4_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-517230573/2500000000 : ℝ)*x 0 + (270867339/500000000 : ℝ)*x 1 + (524077177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517230573/2500000000 : ℝ)^4273 ≤ (2518341366067/20000000000000 : ℝ)^3249 := by
    have hnat : (517230573 : ℕ)^4273*20000000000000^3249 ≤ 2518341366067^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517230573 2500000000 2518341366067 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270867339/500000000 : ℝ)^4273 ≤ (1395510648749/3125000000000 : ℝ)^3249 := by
    have hnat : (270867339 : ℕ)^4273*3125000000000^3249 ≤ 1395510648749^3249*500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270867339 500000000 1395510648749 3125000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524077177/1000000000 : ℝ)^4273 ≤ (42751952389061/100000000000000 : ℝ)^3249 := by
    have hnat : (524077177 : ℕ)^4273*100000000000000^3249 ≤ 42751952389061^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524077177 1000000000 42751952389061 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517230573/2500000000 : ℝ), (270867339/500000000 : ℝ), (524077177/1000000000 : ℝ)] ![(2518341366067/20000000000000 : ℝ), (1395510648749/3125000000000 : ℝ), (42751952389061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517230573/2500000000 : ℝ)|^4273 ≤ (2518341366067/20000000000000 : ℝ)^3249
        have hw : |(-517230573/2500000000 : ℝ)|=(517230573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270867339/500000000 : ℝ)|^4273 ≤ (1395510648749/3125000000000 : ℝ)^3249
        have hw : |(270867339/500000000 : ℝ)|=(270867339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524077177/1000000000 : ℝ)|^4273 ≤ (42751952389061/100000000000000 : ℝ)^3249
        have hw : |(524077177/1000000000 : ℝ)|=(524077177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675138807/5000000000 : ℝ)*x 0 + (-2158973467/10000000000 : ℝ)*x 1 + (104815433/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675138807/5000000000 : ℝ)^4273 ≤ (8786129851721/20000000000000 : ℝ)^3249 := by
    have hnat : (2675138807 : ℕ)^4273*20000000000000^3249 ≤ 8786129851721^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675138807 5000000000 8786129851721 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158973467/10000000000 : ℝ)^4273 ≤ (6658699809929/50000000000000 : ℝ)^3249 := by
    have hnat : (2158973467 : ℕ)^4273*50000000000000^3249 ≤ 6658699809929^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158973467 10000000000 6658699809929 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104815433/200000000 : ℝ)^4273 ≤ (42751951101627/100000000000000 : ℝ)^3249 := by
    have hnat : (104815433 : ℕ)^4273*100000000000000^3249 ≤ 42751951101627^3249*200000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104815433 200000000 42751951101627 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675138807/5000000000 : ℝ), (-2158973467/10000000000 : ℝ), (104815433/200000000 : ℝ)] ![(8786129851721/20000000000000 : ℝ), (6658699809929/50000000000000 : ℝ), (42751951101627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675138807/5000000000 : ℝ)|^4273 ≤ (8786129851721/20000000000000 : ℝ)^3249
        have hw : |(2675138807/5000000000 : ℝ)|=(2675138807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2158973467/10000000000 : ℝ)|^4273 ≤ (6658699809929/50000000000000 : ℝ)^3249
        have hw : |(-2158973467/10000000000 : ℝ)|=(2158973467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104815433/200000000 : ℝ)|^4273 ≤ (42751951101627/100000000000000 : ℝ)^3249
        have hw : |(104815433/200000000 : ℝ)|=(104815433/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350277389/10000000000 : ℝ)*x 0 + (2620385819/5000000000 : ℝ)*x 1 + (-269871723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350277389/10000000000 : ℝ)^4273 ≤ (43930646828881/100000000000000 : ℝ)^3249 := by
    have hnat : (5350277389 : ℕ)^4273*100000000000000^3249 ≤ 43930646828881^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350277389 10000000000 43930646828881 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620385819/5000000000 : ℝ)^4273 ≤ (42751950972883/100000000000000 : ℝ)^3249 := by
    have hnat : (2620385819 : ℕ)^4273*100000000000000^3249 ≤ 42751950972883^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620385819 5000000000 42751950972883 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269871723/1250000000 : ℝ)^4273 ≤ (3329350547881/25000000000000 : ℝ)^3249 := by
    have hnat : (269871723 : ℕ)^4273*25000000000000^3249 ≤ 3329350547881^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269871723 1250000000 3329350547881 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350277389/10000000000 : ℝ), (2620385819/5000000000 : ℝ), (-269871723/1250000000 : ℝ)] ![(43930646828881/100000000000000 : ℝ), (42751950972883/100000000000000 : ℝ), (3329350547881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350277389/10000000000 : ℝ)|^4273 ≤ (43930646828881/100000000000000 : ℝ)^3249
        have hw : |(5350277389/10000000000 : ℝ)|=(5350277389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620385819/5000000000 : ℝ)|^4273 ≤ (42751950972883/100000000000000 : ℝ)^3249
        have hw : |(2620385819/5000000000 : ℝ)|=(2620385819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269871723/1250000000 : ℝ)|^4273 ≤ (3329350547881/25000000000000 : ℝ)^3249
        have hw : |(-269871723/1250000000 : ℝ)|=(269871723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2167020007/5000000000 : ℝ)*x 0 + (2077392517/5000000000 : ℝ)*x 1 + (4520603101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167020007/5000000000 : ℝ)^4273 ≤ (33300521988411/100000000000000 : ℝ)^3249 := by
    have hnat : (2167020007 : ℕ)^4273*100000000000000^3249 ≤ 33300521988411^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167020007 5000000000 33300521988411 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077392517/5000000000 : ℝ)^4273 ≤ (7875262322613/25000000000000 : ℝ)^3249 := by
    have hnat : (2077392517 : ℕ)^4273*25000000000000^3249 ≤ 7875262322613^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077392517 5000000000 7875262322613 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520603101/10000000000 : ℝ)^4273 ≤ (17599214356167/50000000000000 : ℝ)^3249 := by
    have hnat : (4520603101 : ℕ)^4273*50000000000000^3249 ≤ 17599214356167^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520603101 10000000000 17599214356167 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167020007/5000000000 : ℝ), (2077392517/5000000000 : ℝ), (4520603101/10000000000 : ℝ)] ![(33300521988411/100000000000000 : ℝ), (7875262322613/25000000000000 : ℝ), (17599214356167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167020007/5000000000 : ℝ)|^4273 ≤ (33300521988411/100000000000000 : ℝ)^3249
        have hw : |(2167020007/5000000000 : ℝ)|=(2167020007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077392517/5000000000 : ℝ)|^4273 ≤ (7875262322613/25000000000000 : ℝ)^3249
        have hw : |(2077392517/5000000000 : ℝ)|=(2077392517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520603101/10000000000 : ℝ)|^4273 ≤ (17599214356167/50000000000000 : ℝ)^3249
        have hw : |(4520603101/10000000000 : ℝ)|=(4520603101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034468033/5000000000 : ℝ)*x 0 + (5241424889/10000000000 : ℝ)*x 1 + (5416690253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034468033/5000000000 : ℝ)^4273 ≤ (6295908540871/50000000000000 : ℝ)^3249 := by
    have hnat : (1034468033 : ℕ)^4273*50000000000000^3249 ≤ 6295908540871^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034468033 5000000000 6295908540871 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241424889/10000000000 : ℝ)^4273 ≤ (21379479796311/50000000000000 : ℝ)^3249 := by
    have hnat : (5241424889 : ℕ)^4273*50000000000000^3249 ≤ 21379479796311^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241424889 10000000000 21379479796311 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416690253/10000000000 : ℝ)^4273 ≤ (44649223317347/100000000000000 : ℝ)^3249 := by
    have hnat : (5416690253 : ℕ)^4273*100000000000000^3249 ≤ 44649223317347^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416690253 10000000000 44649223317347 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034468033/5000000000 : ℝ), (5241424889/10000000000 : ℝ), (5416690253/10000000000 : ℝ)] ![(6295908540871/50000000000000 : ℝ), (21379479796311/50000000000000 : ℝ), (44649223317347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034468033/5000000000 : ℝ)|^4273 ≤ (6295908540871/50000000000000 : ℝ)^3249
        have hw : |(-1034468033/5000000000 : ℝ)|=(1034468033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241424889/10000000000 : ℝ)|^4273 ≤ (21379479796311/50000000000000 : ℝ)^3249
        have hw : |(5241424889/10000000000 : ℝ)|=(5241424889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416690253/10000000000 : ℝ)|^4273 ≤ (44649223317347/100000000000000 : ℝ)^3249
        have hw : |(5416690253/10000000000 : ℝ)|=(5416690253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304952123/10000000000 : ℝ)*x 0 + (-1983054989/10000000000 : ℝ)*x 1 + (5416689799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304952123/10000000000 : ℝ)^4273 ≤ (43441844191437/100000000000000 : ℝ)^3249 := by
    have hnat : (5304952123 : ℕ)^4273*100000000000000^3249 ≤ 43441844191437^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304952123 10000000000 43441844191437 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983054989/10000000000 : ℝ)^4273 ≤ (11908937399583/100000000000000 : ℝ)^3249 := by
    have hnat : (1983054989 : ℕ)^4273*100000000000000^3249 ≤ 11908937399583^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983054989 10000000000 11908937399583 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416689799/10000000000 : ℝ)^4273 ≤ (11162304598901/25000000000000 : ℝ)^3249 := by
    have hnat : (5416689799 : ℕ)^4273*25000000000000^3249 ≤ 11162304598901^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416689799 10000000000 11162304598901 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304952123/10000000000 : ℝ), (-1983054989/10000000000 : ℝ), (5416689799/10000000000 : ℝ)] ![(43441844191437/100000000000000 : ℝ), (11908937399583/100000000000000 : ℝ), (11162304598901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304952123/10000000000 : ℝ)|^4273 ≤ (43441844191437/100000000000000 : ℝ)^3249
        have hw : |(5304952123/10000000000 : ℝ)|=(5304952123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1983054989/10000000000 : ℝ)|^4273 ≤ (11908937399583/100000000000000 : ℝ)^3249
        have hw : |(-1983054989/10000000000 : ℝ)|=(1983054989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416689799/10000000000 : ℝ)|^4273 ≤ (11162304598901/25000000000000 : ℝ)^3249
        have hw : |(5416689799/10000000000 : ℝ)|=(5416689799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652475673/5000000000 : ℝ)*x 0 + (1354172683/2500000000 : ℝ)*x 1 + (-123940923/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652475673/5000000000 : ℝ)^4273 ≤ (21720917911629/50000000000000 : ℝ)^3249 := by
    have hnat : (2652475673 : ℕ)^4273*50000000000000^3249 ≤ 21720917911629^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652475673 5000000000 21720917911629 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354172683/2500000000 : ℝ)^4273 ≤ (44649228510111/100000000000000 : ℝ)^3249 := by
    have hnat : (1354172683 : ℕ)^4273*100000000000000^3249 ≤ 44649228510111^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354172683 2500000000 44649228510111 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123940923/625000000 : ℝ)^4273 ≤ (2977233913527/25000000000000 : ℝ)^3249 := by
    have hnat : (123940923 : ℕ)^4273*25000000000000^3249 ≤ 2977233913527^3249*625000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123940923 625000000 2977233913527 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652475673/5000000000 : ℝ), (1354172683/2500000000 : ℝ), (-123940923/625000000 : ℝ)] ![(21720917911629/50000000000000 : ℝ), (44649228510111/100000000000000 : ℝ), (2977233913527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652475673/5000000000 : ℝ)|^4273 ≤ (21720917911629/50000000000000 : ℝ)^3249
        have hw : |(2652475673/5000000000 : ℝ)|=(2652475673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354172683/2500000000 : ℝ)|^4273 ≤ (44649228510111/100000000000000 : ℝ)^3249
        have hw : |(1354172683/2500000000 : ℝ)|=(1354172683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123940923/625000000 : ℝ)|^4273 ≤ (2977233913527/25000000000000 : ℝ)^3249
        have hw : |(-123940923/625000000 : ℝ)|=(123940923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s4_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (866813739/2000000000 : ℝ)*x 0 + (4519250509/10000000000 : ℝ)*x 1 + (51951811/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866813739/2000000000 : ℝ)^4273 ≤ (33300811813547/100000000000000 : ℝ)^3249 := by
    have hnat : (866813739 : ℕ)^4273*100000000000000^3249 ≤ 33300811813547^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866813739 2000000000 33300811813547 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519250509/10000000000 : ℝ)^4273 ≤ (35184578500537/100000000000000 : ℝ)^3249 := by
    have hnat : (4519250509 : ℕ)^4273*100000000000000^3249 ≤ 35184578500537^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519250509 10000000000 35184578500537 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51951811/125000000 : ℝ)^4273 ≤ (7878652416903/25000000000000 : ℝ)^3249 := by
    have hnat : (51951811 : ℕ)^4273*25000000000000^3249 ≤ 7878652416903^3249*125000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51951811 125000000 7878652416903 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866813739/2000000000 : ℝ), (4519250509/10000000000 : ℝ), (51951811/125000000 : ℝ)] ![(33300811813547/100000000000000 : ℝ), (35184578500537/100000000000000 : ℝ), (7878652416903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866813739/2000000000 : ℝ)|^4273 ≤ (33300811813547/100000000000000 : ℝ)^3249
        have hw : |(866813739/2000000000 : ℝ)|=(866813739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519250509/10000000000 : ℝ)|^4273 ≤ (35184578500537/100000000000000 : ℝ)^3249
        have hw : |(4519250509/10000000000 : ℝ)|=(4519250509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51951811/125000000 : ℝ)|^4273 ≤ (7878652416903/25000000000000 : ℝ)^3249
        have hw : |(51951811/125000000 : ℝ)|=(51951811/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (94/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (94/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2687/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (94/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2687/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (94/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2687/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (94/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2687/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (94/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2687/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (94/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2687/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2687/25000 : ℝ) ^ (267/64 : ℝ) ≤ (2273840936339323/25000000000000000000 : ℝ) := by
    have hpowers : (2687/25000 : ℝ)^267 ≤ (2273840936339323/25000000000000000000 : ℝ)^64 := by
      have hnat : (2687 : ℕ)^267*25000000000000000000^64 ≤ 2273840936339323^64*25000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2687 25000 2273840936339323 25000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2687/25000 : ℝ)) (X := (2273840936339323/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (94/625 : ℝ) ^ (267/64 : ℝ) ≤ (1847356960290643/5000000000000000000 : ℝ) := by
    have hpowers : (94/625 : ℝ)^267 ≤ (1847356960290643/5000000000000000000 : ℝ)^64 := by
      have hnat : (94 : ℕ)^267*5000000000000000000^64 ≤ 1847356960290643^64*625^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94 625 1847356960290643 5000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (94/625 : ℝ)) (X := (1847356960290643/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502273840936339323/12500000000000000000 : ℝ) ≤ (10000436002269951/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (12502273840936339323/12500000000000000000 : ℝ)^64 ≤ (10000436002269951/10000000000000000 : ℝ)^267 := by
      have hnat : (12502273840936339323 : ℕ)^64*10000000000000000^267 ≤ 10000436002269951^267*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502273840936339323 12500000000000000000 10000436002269951 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000436002269951/10000000000000000 : ℝ)) (X := (12502273840936339323/12500000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505755312868896269/12500000000000000000 : ℝ) ≤ (1000110344740161/1000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (12505755312868896269/12500000000000000000 : ℝ)^64 ≤ (1000110344740161/1000000000000000 : ℝ)^267 := by
      have hnat : (12505755312868896269 : ℕ)^64*1000000000000000^267 ≤ 1000110344740161^267*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505755312868896269 12500000000000000000 1000110344740161 1000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000110344740161/1000000000000000 : ℝ)) (X := (12505755312868896269/12500000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501847356960290643/2500000000000000000 : ℝ) ≤ (10001770892533269/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (2501847356960290643/2500000000000000000 : ℝ)^64 ≤ (10001770892533269/10000000000000000 : ℝ)^267 := by
      have hnat : (2501847356960290643 : ℕ)^64*10000000000000000^267 ≤ 10001770892533269^267*2500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501847356960290643 2500000000000000000 10001770892533269 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001770892533269/10000000000000000 : ℝ)) (X := (2501847356960290643/2500000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2273840936339323/25000000000000000000 : ℝ) ≤ ((10726880980298121957/10730000000000000000 : ℝ)+2*(667445131659/429200000000000 : ℝ)*(2687/25000 : ℝ))^(267/64 : ℝ) := by
    rw [show (10726880980298121957/10730000000000000000 : ℝ)+2*(667445131659/429200000000000 : ℝ)*(2687/25000 : ℝ)=(10000436002269951/10000000000000000 : ℝ) by norm_num, show 1+2*(2273840936339323/25000000000000000000 : ℝ)=(12502273840936339323/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1847356960290643/5000000000000000000 : ℝ)+(2273840936339323/25000000000000000000 : ℝ) ≤ ((10726880980298121957/10730000000000000000 : ℝ)+(667445131659/429200000000000 : ℝ)*((94/625 : ℝ)+(2687/25000 : ℝ)))^(267/64 : ℝ) := by
    rw [show (10726880980298121957/10730000000000000000 : ℝ)+(667445131659/429200000000000 : ℝ)*((94/625 : ℝ)+(2687/25000 : ℝ))=(1000110344740161/1000000000000000 : ℝ) by norm_num, show 1+(1847356960290643/5000000000000000000 : ℝ)+(2273840936339323/25000000000000000000 : ℝ)=(12505755312868896269/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1847356960290643/5000000000000000000 : ℝ) ≤ ((10726880980298121957/10730000000000000000 : ℝ)+2*(667445131659/429200000000000 : ℝ)*(94/625 : ℝ))^(267/64 : ℝ) := by
    rw [show (10726880980298121957/10730000000000000000 : ℝ)+2*(667445131659/429200000000000 : ℝ)*(94/625 : ℝ)=(10001770892533269/10000000000000000 : ℝ) by norm_num, show 1+2*(1847356960290643/5000000000000000000 : ℝ)=(2501847356960290643/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10726880980298121957/10730000000000000000 : ℝ)*(X 1 0+X 2 0)+(667445131659/429200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (94/625 : ℝ)) (c := (10726880980298121957/10730000000000000000 : ℝ)) (alpha := (667445131659/429200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10726880980298121957/10730000000000000000 : ℝ)*(X 0 1+X 2 1)+(667445131659/429200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (94/625 : ℝ)) (c := (10726880980298121957/10730000000000000000 : ℝ)) (alpha := (667445131659/429200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10726880980298121957/10730000000000000000 : ℝ)*(X 0 2+X 1 2)+(667445131659/429200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (94/625 : ℝ)) (c := (10726880980298121957/10730000000000000000 : ℝ)) (alpha := (667445131659/429200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517230573/2500000000 : ℝ)*X 0 0+(270867339/500000000 : ℝ)*X 0 1+(524077177/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675138807/5000000000 : ℝ)*X 1 0+(-2158973467/10000000000 : ℝ)*X 1 1+(104815433/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350277389/10000000000 : ℝ)*X 2 0+(2620385819/5000000000 : ℝ)*X 2 1+(-269871723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2167020007/5000000000 : ℝ)*X 0 0+(2077392517/5000000000 : ℝ)*X 0 1+(4520603101/10000000000 : ℝ)*X 0 2+(2167020007/5000000000 : ℝ)*X 1 0+(2077392517/5000000000 : ℝ)*X 1 1+(4520603101/10000000000 : ℝ)*X 1 2+(2167020007/5000000000 : ℝ)*X 2 0+(2077392517/5000000000 : ℝ)*X 2 1+(4520603101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1034468033/5000000000 : ℝ)*X 0 0+(5241424889/10000000000 : ℝ)*X 0 1+(5416690253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304952123/10000000000 : ℝ)*X 1 0+(-1983054989/10000000000 : ℝ)*X 1 1+(5416689799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652475673/5000000000 : ℝ)*X 2 0+(1354172683/2500000000 : ℝ)*X 2 1+(-123940923/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866813739/2000000000 : ℝ)*X 0 0+(4519250509/10000000000 : ℝ)*X 0 1+(51951811/125000000 : ℝ)*X 0 2+(866813739/2000000000 : ℝ)*X 1 0+(4519250509/10000000000 : ℝ)*X 1 1+(51951811/125000000 : ℝ)*X 1 2+(866813739/2000000000 : ℝ)*X 2 0+(4519250509/10000000000 : ℝ)*X 2 1+(51951811/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631600552248082063910572251/107300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252699403/20000000000000 : ℝ)*(base19) + (1117896169/100000000000000 : ℝ)*(base23) + (4263431/2000000000000 : ℝ)*(upper3) + (64060481/100000000000000 : ℝ)*(lower4) + (839698770012219/20000000000000 : ℝ)*(major0) + (839698770012219/20000000000000 : ℝ)*(major1) + (839698770012219/20000000000000 : ℝ)*(major2) + (1415836143823693/25000000000000 : ℝ)*(sp0) + (226534460525433/4000000000000 : ℝ)*(sp1) + (1132671690379209/20000000000000 : ℝ)*(sp2) + (341701393224929/12500000000000 : ℝ)*(sp3) + (4550334517/25000000000000 : ℝ)*(sp4) + (1603420313/50000000000000 : ℝ)*(sp6) + (13581479739/100000000000000 : ℝ)*(sp7) + (273362472727917/10000000000000 : ℝ)*(f.failure) + (141584069415821/2500000000000 : ℝ)*(f.sum) + (34678784047051/4292000000000000000000000000 : ℝ)*base66 + (300045170790617583/214600000000000000000000000000000 : ℝ)*base67 + (763878146073617583/214600000000000000000000000000000 : ℝ)*base69 + (1560626478788582417/214600000000000000000000000000000 : ℝ)*base72 + (22097892623367/4292000000000000000000000000 : ℝ)*base74 + (927033460226017583/214600000000000000000000000000000 : ℝ)*base75 + (1098420412766817583/214600000000000000000000000000000 : ℝ)*base77 + (655405818627382417/214600000000000000000000000000000 : ℝ)*base80 + (14767385558647/4292000000000000000000000000 : ℝ)*base82 + (97701/50000000000000000000 : ℝ)*base89 + (97701/50000000000000000000 : ℝ)*base91 + (97701/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (384020354662557347239309413/67062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1550380323/100000000000000 : ℝ)*(base19) + (1008215217/100000000000000 : ℝ)*(base23) + (138649233/100000000000000 : ℝ)*(upper3) + (103000867/100000000000000 : ℝ)*(lower4) + (528727751909197/12500000000000 : ℝ)*(major0) + (528727751909197/12500000000000 : ℝ)*(major1) + (528727751909197/12500000000000 : ℝ)*(major2) + (8893424271/50000000000000 : ℝ)*(sp1) + (1470783717/5000000000000 : ℝ)*(sp2) + (257984007/12500000000000 : ℝ)*(sp3) + (713202681637629/12500000000000 : ℝ)*(sp4) + (2852801057936083/50000000000000 : ℝ)*(sp5) + (228223641168459/4000000000000 : ℝ)*(sp6) + (1377010161348607/50000000000000 : ℝ)*(sp7) + (275402238656927/10000000000000 : ℝ)*(f.failure) + (713202681637629/12500000000000 : ℝ)*(f.sum) + (7684330195271/1341250000000000000000000000 : ℝ)*base66 + (642556537079763529/134125000000000000000000000000000 : ℝ)*base67 + (537795014459513529/134125000000000000000000000000000 : ℝ)*base69 + (245972557453486471/134125000000000000000000000000000 : ℝ)*base72 + (749830159023/670625000000000000000000000 : ℝ)*base74 + (181152905687763529/134125000000000000000000000000000 : ℝ)*base75 + (261027131110013529/134125000000000000000000000000000 : ℝ)*base77 + (197137474614736471/134125000000000000000000000000000 : ℝ)*base80 + (1633828785403/2682500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (328231/50000000000000000000 : ℝ)*base89 + (328231/50000000000000000000 : ℝ)*base91 + (328231/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1313_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (94/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1313_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1313_s5_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069230329/10000000000 : ℝ)*x 0 + (2707352003/5000000000 : ℝ)*x 1 + (5243212083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069230329/10000000000 : ℝ)^4273 ≤ (12594172510153/100000000000000 : ℝ)^3249 := by
    have hnat : (2069230329 : ℕ)^4273*100000000000000^3249 ≤ 12594172510153^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069230329 10000000000 12594172510153 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707352003/5000000000 : ℝ)^4273 ≤ (2789230748011/6250000000000 : ℝ)^3249 := by
    have hnat : (2707352003 : ℕ)^4273*6250000000000^3249 ≤ 2789230748011^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707352003 5000000000 2789230748011 6250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243212083/10000000000 : ℝ)^4273 ≤ (42778135502309/100000000000000 : ℝ)^3249 := by
    have hnat : (5243212083 : ℕ)^4273*100000000000000^3249 ≤ 42778135502309^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243212083 10000000000 42778135502309 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069230329/10000000000 : ℝ), (2707352003/5000000000 : ℝ), (5243212083/10000000000 : ℝ)] ![(12594172510153/100000000000000 : ℝ), (2789230748011/6250000000000 : ℝ), (42778135502309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069230329/10000000000 : ℝ)|^4273 ≤ (12594172510153/100000000000000 : ℝ)^3249
        have hw : |(-2069230329/10000000000 : ℝ)|=(2069230329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707352003/5000000000 : ℝ)|^4273 ≤ (2789230748011/6250000000000 : ℝ)^3249
        have hw : |(2707352003/5000000000 : ℝ)|=(2707352003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243212083/10000000000 : ℝ)|^4273 ≤ (42778135502309/100000000000000 : ℝ)^3249
        have hw : |(5243212083/10000000000 : ℝ)|=(5243212083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069921079/2000000000 : ℝ)*x 0 + (-2156640237/10000000000 : ℝ)*x 1 + (2621606029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069921079/2000000000 : ℝ)^4273 ≤ (43923390260711/100000000000000 : ℝ)^3249 := by
    have hnat : (1069921079 : ℕ)^4273*100000000000000^3249 ≤ 43923390260711^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069921079 2000000000 43923390260711 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156640237/10000000000 : ℝ)^4273 ≤ (6649237244903/50000000000000 : ℝ)^3249 := by
    have hnat : (2156640237 : ℕ)^4273*50000000000000^3249 ≤ 6649237244903^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156640237 10000000000 6649237244903 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621606029/5000000000 : ℝ)^4273 ≤ (21389067617027/50000000000000 : ℝ)^3249 := by
    have hnat : (2621606029 : ℕ)^4273*50000000000000^3249 ≤ 21389067617027^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621606029 5000000000 21389067617027 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069921079/2000000000 : ℝ), (-2156640237/10000000000 : ℝ), (2621606029/5000000000 : ℝ)] ![(43923390260711/100000000000000 : ℝ), (6649237244903/50000000000000 : ℝ), (21389067617027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069921079/2000000000 : ℝ)|^4273 ≤ (43923390260711/100000000000000 : ℝ)^3249
        have hw : |(1069921079/2000000000 : ℝ)|=(1069921079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156640237/10000000000 : ℝ)|^4273 ≤ (6649237244903/50000000000000 : ℝ)^3249
        have hw : |(-2156640237/10000000000 : ℝ)|=(2156640237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621606029/5000000000 : ℝ)|^4273 ≤ (21389067617027/50000000000000 : ℝ)^3249
        have hw : |(2621606029/5000000000 : ℝ)|=(2621606029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668700693/1250000000 : ℝ)*x 0 + (5243212041/10000000000 : ℝ)*x 1 + (-2156640061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668700693/1250000000 : ℝ)^4273 ≤ (8784678373933/20000000000000 : ℝ)^3249 := by
    have hnat : (668700693 : ℕ)^4273*20000000000000^3249 ≤ 8784678373933^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668700693 1250000000 8784678373933 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243212041/10000000000 : ℝ)^4273 ≤ (42778135051641/100000000000000 : ℝ)^3249 := by
    have hnat : (5243212041 : ℕ)^4273*100000000000000^3249 ≤ 42778135051641^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243212041 10000000000 42778135051641 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156640061/10000000000 : ℝ)^4273 ≤ (13298473062491/100000000000000 : ℝ)^3249 := by
    have hnat : (2156640061 : ℕ)^4273*100000000000000^3249 ≤ 13298473062491^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156640061 10000000000 13298473062491 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668700693/1250000000 : ℝ), (5243212041/10000000000 : ℝ), (-2156640061/10000000000 : ℝ)] ![(8784678373933/20000000000000 : ℝ), (42778135051641/100000000000000 : ℝ), (13298473062491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668700693/1250000000 : ℝ)|^4273 ≤ (8784678373933/20000000000000 : ℝ)^3249
        have hw : |(668700693/1250000000 : ℝ)|=(668700693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243212041/10000000000 : ℝ)|^4273 ≤ (42778135051641/100000000000000 : ℝ)^3249
        have hw : |(5243212041/10000000000 : ℝ)|=(5243212041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156640061/10000000000 : ℝ)|^4273 ≤ (13298473062491/100000000000000 : ℝ)^3249
        have hw : |(-2156640061/10000000000 : ℝ)|=(2156640061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334224259/10000000000 : ℝ)*x 0 + (2080013743/5000000000 : ℝ)*x 1 + (4515314433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334224259/10000000000 : ℝ)^4273 ≤ (4162797977249/12500000000000 : ℝ)^3249 := by
    have hnat : (4334224259 : ℕ)^4273*12500000000000^3249 ≤ 4162797977249^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334224259 10000000000 4162797977249 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080013743/5000000000 : ℝ)^4273 ≤ (986041709051/3125000000000 : ℝ)^3249 := by
    have hnat : (2080013743 : ℕ)^4273*3125000000000^3249 ≤ 986041709051^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080013743 5000000000 986041709051 3125000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515314433/10000000000 : ℝ)^4273 ≤ (137282349519/390625000000 : ℝ)^3249 := by
    have hnat : (4515314433 : ℕ)^4273*390625000000^3249 ≤ 137282349519^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515314433 10000000000 137282349519 390625000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334224259/10000000000 : ℝ), (2080013743/5000000000 : ℝ), (4515314433/10000000000 : ℝ)] ![(4162797977249/12500000000000 : ℝ), (986041709051/3125000000000 : ℝ), (137282349519/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334224259/10000000000 : ℝ)|^4273 ≤ (4162797977249/12500000000000 : ℝ)^3249
        have hw : |(4334224259/10000000000 : ℝ)|=(4334224259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080013743/5000000000 : ℝ)|^4273 ≤ (986041709051/3125000000000 : ℝ)^3249
        have hw : |(2080013743/5000000000 : ℝ)|=(2080013743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515314433/10000000000 : ℝ)|^4273 ≤ (137282349519/390625000000 : ℝ)^3249
        have hw : |(4515314433/10000000000 : ℝ)|=(4515314433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069243239/10000000000 : ℝ)*x 0 + (2621914083/5000000000 : ℝ)*x 1 + (1082816917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069243239/10000000000 : ℝ)^4273 ≤ (503771034027/4000000000000 : ℝ)^3249 := by
    have hnat : (2069243239 : ℕ)^4273*4000000000000^3249 ≤ 503771034027^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069243239 10000000000 503771034027 4000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621914083/5000000000 : ℝ)^4273 ≤ (42784746315347/100000000000000 : ℝ)^3249 := by
    have hnat : (2621914083 : ℕ)^4273*100000000000000^3249 ≤ 42784746315347^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621914083 5000000000 42784746315347 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082816917/2000000000 : ℝ)^4273 ≤ (11155244454763/25000000000000 : ℝ)^3249 := by
    have hnat : (1082816917 : ℕ)^4273*25000000000000^3249 ≤ 11155244454763^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082816917 2000000000 11155244454763 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069243239/10000000000 : ℝ), (2621914083/5000000000 : ℝ), (1082816917/2000000000 : ℝ)] ![(503771034027/4000000000000 : ℝ), (42784746315347/100000000000000 : ℝ), (11155244454763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069243239/10000000000 : ℝ)|^4273 ≤ (503771034027/4000000000000 : ℝ)^3249
        have hw : |(-2069243239/10000000000 : ℝ)|=(2069243239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621914083/5000000000 : ℝ)|^4273 ≤ (42784746315347/100000000000000 : ℝ)^3249
        have hw : |(2621914083/5000000000 : ℝ)|=(2621914083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082816917/2000000000 : ℝ)|^4273 ≤ (11155244454763/25000000000000 : ℝ)^3249
        have hw : |(1082816917/2000000000 : ℝ)|=(1082816917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305584477/10000000000 : ℝ)*x 0 + (-248220931/1250000000 : ℝ)*x 1 + (5414084793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305584477/10000000000 : ℝ)^4273 ≤ (21724327340989/50000000000000 : ℝ)^3249 := by
    have hnat : (5305584477 : ℕ)^4273*50000000000000^3249 ≤ 21724327340989^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305584477 10000000000 21724327340989 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248220931/1250000000 : ℝ)^4273 ≤ (5965182614789/50000000000000 : ℝ)^3249 := by
    have hnat : (248220931 : ℕ)^4273*50000000000000^3249 ≤ 5965182614789^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248220931 1250000000 5965182614789 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414084793/10000000000 : ℝ)^4273 ≤ (22310490036803/50000000000000 : ℝ)^3249 := by
    have hnat : (5414084793 : ℕ)^4273*50000000000000^3249 ≤ 22310490036803^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414084793 10000000000 22310490036803 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305584477/10000000000 : ℝ), (-248220931/1250000000 : ℝ), (5414084793/10000000000 : ℝ)] ![(21724327340989/50000000000000 : ℝ), (5965182614789/50000000000000 : ℝ), (22310490036803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305584477/10000000000 : ℝ)|^4273 ≤ (21724327340989/50000000000000 : ℝ)^3249
        have hw : |(5305584477/10000000000 : ℝ)|=(5305584477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248220931/1250000000 : ℝ)|^4273 ≤ (5965182614789/50000000000000 : ℝ)^3249
        have hw : |(-248220931/1250000000 : ℝ)|=(248220931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414084793/10000000000 : ℝ)|^4273 ≤ (22310490036803/50000000000000 : ℝ)^3249
        have hw : |(5414084793/10000000000 : ℝ)|=(5414084793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652792469/5000000000 : ℝ)*x 0 + (5414084701/10000000000 : ℝ)*x 1 + (-397153389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652792469/5000000000 : ℝ)^4273 ≤ (43448659647069/100000000000000 : ℝ)^3249 := by
    have hnat : (2652792469 : ℕ)^4273*100000000000000^3249 ≤ 43448659647069^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652792469 5000000000 43448659647069 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414084701/10000000000 : ℝ)^4273 ≤ (44620979076399/100000000000000 : ℝ)^3249 := by
    have hnat : (5414084701 : ℕ)^4273*100000000000000^3249 ≤ 44620979076399^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414084701 10000000000 44620979076399 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397153389/2000000000 : ℝ)^4273 ≤ (11930361255133/100000000000000 : ℝ)^3249 := by
    have hnat : (397153389 : ℕ)^4273*100000000000000^3249 ≤ 11930361255133^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397153389 2000000000 11930361255133 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652792469/5000000000 : ℝ), (5414084701/10000000000 : ℝ), (-397153389/2000000000 : ℝ)] ![(43448659647069/100000000000000 : ℝ), (44620979076399/100000000000000 : ℝ), (11930361255133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652792469/5000000000 : ℝ)|^4273 ≤ (43448659647069/100000000000000 : ℝ)^3249
        have hw : |(2652792469/5000000000 : ℝ)|=(2652792469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414084701/10000000000 : ℝ)|^4273 ≤ (44620979076399/100000000000000 : ℝ)^3249
        have hw : |(5414084701/10000000000 : ℝ)|=(5414084701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397153389/2000000000 : ℝ)|^4273 ≤ (11930361255133/100000000000000 : ℝ)^3249
        have hw : |(-397153389/2000000000 : ℝ)|=(397153389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s5_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083562667/2500000000 : ℝ)*x 0 + (4514038307/10000000000 : ℝ)*x 1 + (416131013/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083562667/2500000000 : ℝ)^4273 ≤ (16651325343917/50000000000000 : ℝ)^3249 := by
    have hnat : (1083562667 : ℕ)^4273*50000000000000^3249 ≤ 16651325343917^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083562667 2500000000 16651325343917 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514038307/10000000000 : ℝ)^4273 ≤ (35131219044207/100000000000000 : ℝ)^3249 := by
    have hnat : (4514038307 : ℕ)^4273*100000000000000^3249 ≤ 35131219044207^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514038307 10000000000 35131219044207 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416131013/1000000000 : ℝ)^4273 ≤ (1262645210199/4000000000000 : ℝ)^3249 := by
    have hnat : (416131013 : ℕ)^4273*4000000000000^3249 ≤ 1262645210199^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416131013 1000000000 1262645210199 4000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083562667/2500000000 : ℝ), (4514038307/10000000000 : ℝ), (416131013/1000000000 : ℝ)] ![(16651325343917/50000000000000 : ℝ), (35131219044207/100000000000000 : ℝ), (1262645210199/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083562667/2500000000 : ℝ)|^4273 ≤ (16651325343917/50000000000000 : ℝ)^3249
        have hw : |(1083562667/2500000000 : ℝ)|=(1083562667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514038307/10000000000 : ℝ)|^4273 ≤ (35131219044207/100000000000000 : ℝ)^3249
        have hw : |(4514038307/10000000000 : ℝ)|=(4514038307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416131013/1000000000 : ℝ)|^4273 ≤ (1262645210199/4000000000000 : ℝ)^3249
        have hw : |(416131013/1000000000 : ℝ)|=(416131013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11069/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11017/100000 : ℝ) ^ (267/64 : ℝ) ≤ (5041712076617827/50000000000000000000 : ℝ) := by
    have hpowers : (11017/100000 : ℝ)^267 ≤ (5041712076617827/50000000000000000000 : ℝ)^64 := by
      have hnat : (11017 : ℕ)^267*50000000000000000000^64 ≤ 5041712076617827^64*100000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11017 100000 5041712076617827 50000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11017/100000 : ℝ)) (X := (5041712076617827/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (267/64 : ℝ) ≤ (6820645540579857/20000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^267 ≤ (6820645540579857/20000000000000000000 : ℝ)^64 := by
      have hnat : (7377 : ℕ)^267*20000000000000000000^64 ≤ 6820645540579857^64*50000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 6820645540579857 20000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (6820645540579857/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005041712076617827/25000000000000000000 : ℝ) ≤ (1250060420381763/1250000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (25005041712076617827/25000000000000000000 : ℝ)^64 ≤ (1250060420381763/1250000000000000 : ℝ)^267 := by
      have hnat : (25005041712076617827 : ℕ)^64*1250000000000000^267 ≤ 1250060420381763^267*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005041712076617827 25000000000000000000 1250060420381763 1250000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250060420381763/1250000000000000 : ℝ)) (X := (25005041712076617827/25000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044186651856134939/100000000000000000000 : ℝ) ≤ (2000211795566771/2000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (100044186651856134939/100000000000000000000 : ℝ)^64 ≤ (2000211795566771/2000000000000000 : ℝ)^267 := by
      have hnat : (100044186651856134939 : ℕ)^64*2000000000000000^267 ≤ 2000211795566771^267*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044186651856134939 100000000000000000000 2000211795566771 2000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000211795566771/2000000000000000 : ℝ)) (X := (100044186651856134939/100000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006820645540579857/10000000000000000000 : ℝ) ≤ (5000817296306803/5000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (10006820645540579857/10000000000000000000 : ℝ)^64 ≤ (5000817296306803/5000000000000000 : ℝ)^267 := by
      have hnat : (10006820645540579857 : ℕ)^64*5000000000000000^267 ≤ 5000817296306803^267*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006820645540579857 10000000000000000000 5000817296306803 5000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000817296306803/5000000000000000 : ℝ)) (X := (10006820645540579857/10000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5041712076617827/50000000000000000000 : ℝ) ≤ ((18679561615838076557/18685000000000000000 : ℝ)+2*(575614779751/373700000000000 : ℝ)*(11017/100000 : ℝ))^(267/64 : ℝ) := by
    rw [show (18679561615838076557/18685000000000000000 : ℝ)+2*(575614779751/373700000000000 : ℝ)*(11017/100000 : ℝ)=(1250060420381763/1250000000000000 : ℝ) by norm_num, show 1+2*(5041712076617827/50000000000000000000 : ℝ)=(25005041712076617827/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6820645540579857/20000000000000000000 : ℝ)+(5041712076617827/50000000000000000000 : ℝ) ≤ ((18679561615838076557/18685000000000000000 : ℝ)+(575614779751/373700000000000 : ℝ)*((7377/50000 : ℝ)+(11017/100000 : ℝ)))^(267/64 : ℝ) := by
    rw [show (18679561615838076557/18685000000000000000 : ℝ)+(575614779751/373700000000000 : ℝ)*((7377/50000 : ℝ)+(11017/100000 : ℝ))=(2000211795566771/2000000000000000 : ℝ) by norm_num, show 1+(6820645540579857/20000000000000000000 : ℝ)+(5041712076617827/50000000000000000000 : ℝ)=(100044186651856134939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6820645540579857/20000000000000000000 : ℝ) ≤ ((18679561615838076557/18685000000000000000 : ℝ)+2*(575614779751/373700000000000 : ℝ)*(7377/50000 : ℝ))^(267/64 : ℝ) := by
    rw [show (18679561615838076557/18685000000000000000 : ℝ)+2*(575614779751/373700000000000 : ℝ)*(7377/50000 : ℝ)=(5000817296306803/5000000000000000 : ℝ) by norm_num, show 1+2*(6820645540579857/20000000000000000000 : ℝ)=(10006820645540579857/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18679561615838076557/18685000000000000000 : ℝ)*(X 1 0+X 2 0)+(575614779751/373700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18679561615838076557/18685000000000000000 : ℝ)) (alpha := (575614779751/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18679561615838076557/18685000000000000000 : ℝ)*(X 0 1+X 2 1)+(575614779751/373700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18679561615838076557/18685000000000000000 : ℝ)) (alpha := (575614779751/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18679561615838076557/18685000000000000000 : ℝ)*(X 0 2+X 1 2)+(575614779751/373700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18679561615838076557/18685000000000000000 : ℝ)) (alpha := (575614779751/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2069230329/10000000000 : ℝ)*X 0 0+(2707352003/5000000000 : ℝ)*X 0 1+(5243212083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069921079/2000000000 : ℝ)*X 1 0+(-2156640237/10000000000 : ℝ)*X 1 1+(2621606029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668700693/1250000000 : ℝ)*X 2 0+(5243212041/10000000000 : ℝ)*X 2 1+(-2156640061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4334224259/10000000000 : ℝ)*X 0 0+(2080013743/5000000000 : ℝ)*X 0 1+(4515314433/10000000000 : ℝ)*X 0 2+(4334224259/10000000000 : ℝ)*X 1 0+(2080013743/5000000000 : ℝ)*X 1 1+(4515314433/10000000000 : ℝ)*X 1 2+(4334224259/10000000000 : ℝ)*X 2 0+(2080013743/5000000000 : ℝ)*X 2 1+(4515314433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2069243239/10000000000 : ℝ)*X 0 0+(2621914083/5000000000 : ℝ)*X 0 1+(1082816917/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305584477/10000000000 : ℝ)*X 1 0+(-248220931/1250000000 : ℝ)*X 1 1+(5414084793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652792469/5000000000 : ℝ)*X 2 0+(5414084701/10000000000 : ℝ)*X 2 1+(-397153389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083562667/2500000000 : ℝ)*X 0 0+(4514038307/10000000000 : ℝ)*X 0 1+(416131013/1000000000 : ℝ)*X 0 2+(1083562667/2500000000 : ℝ)*X 1 0+(4514038307/10000000000 : ℝ)*X 1 1+(416131013/1000000000 : ℝ)*X 1 2+(1083562667/2500000000 : ℝ)*X 2 0+(4514038307/10000000000 : ℝ)*X 2 1+(416131013/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3321233053619358647411166369/467125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311338903/25000000000000 : ℝ)*(base19) + (626335169/50000000000000 : ℝ)*(base23) + (82972161/100000000000000 : ℝ)*(lower2) + (102396013/100000000000000 : ℝ)*(upper3) + (45562961/20000000000000 : ℝ)*(upper5) + (2161469107533413/50000000000000 : ℝ)*(major0) + (2161469107533413/50000000000000 : ℝ)*(major1) + (2161469107533413/50000000000000 : ℝ)*(major2) + (2915599175147423/50000000000000 : ℝ)*(sp0) + (5831224927741179/100000000000000 : ℝ)*(sp1) + (5831224920426453/100000000000000 : ℝ)*(sp2) + (1407319218917107/50000000000000 : ℝ)*(sp3) + (5564560389/20000000000000 : ℝ)*(sp4) + (11582204471/100000000000000 : ℝ)*(sp7) + (703662505009671/25000000000000 : ℝ)*(f.failure) + (5831226173096791/100000000000000 : ℝ)*(f.sum) + (50899130912801/18685000000000000000000000000 : ℝ)*base65 + (17360988370497100959/934250000000000000000000000000000 : ℝ)*base68 + (15437396944736100959/934250000000000000000000000000000 : ℝ)*base70 + (7020786177058100959/934250000000000000000000000000000 : ℝ)*base72 + (20339293182651/4671250000000000000000000000 : ℝ)*base74 + (9218649955946850959/934250000000000000000000000000000 : ℝ)*base76 + (12132063000757850959/934250000000000000000000000000000 : ℝ)*base78 + (3418787558271850959/934250000000000000000000000000000 : ℝ)*base80 + (23366613779089/18685000000000000000000000000 : ℝ)*base82 + (477137/125000000000000000000 : ℝ)*base90 + (477137/125000000000000000000 : ℝ)*base92 + (477137/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6152435729651297191746676059/934250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1685550381/100000000000000 : ℝ)*(base19) + (153444597/6250000000000 : ℝ)*(base23) + (15985987/100000000000000 : ℝ)*(upper2) + (13751693/4000000000000 : ℝ)*(upper3) + (276397/250000000000 : ℝ)*(upper5) + (4354270287096371/100000000000000 : ℝ)*(major0) + (4354270287096371/100000000000000 : ℝ)*(major1) + (4354270287096371/100000000000000 : ℝ)*(major2) + (6453403851/20000000000000 : ℝ)*(sp1) + (59878061471/100000000000000 : ℝ)*(sp2) + (1468372532908677/25000000000000 : ℝ)*(sp4) + (367091011191567/6250000000000 : ℝ)*(sp5) + (2936713899229843/50000000000000 : ℝ)*(sp6) + (708762555760943/25000000000000 : ℝ)*(sp7) + (708762555760943/25000000000000 : ℝ)*(f.failure) + (1468372532908677/25000000000000 : ℝ)*(f.sum) + (112687220159919/18685000000000000000000000000 : ℝ)*base66 + (3319635626773924647/1868500000000000000000000000000000 : ℝ)*base67 + (13340334537674075353/1868500000000000000000000000000000 : ℝ)*base70 + (13740917403413424647/1868500000000000000000000000000000 : ℝ)*base71 + (3679208461087/583906250000000000000000000 : ℝ)*base74 + (2779120218164924647/1868500000000000000000000000000000 : ℝ)*base75 + (29950660226662075353/1868500000000000000000000000000000 : ℝ)*base78 + (32487573351747424647/1868500000000000000000000000000000 : ℝ)*base79 + (55095833954647/9342500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1159879/125000000000000000000 : ℝ)*base89 + (1159879/125000000000000000000 : ℝ)*base91 + (1159879/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1313_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1313_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1313_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1931/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1313_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1313_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1313_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1931/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1313_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
