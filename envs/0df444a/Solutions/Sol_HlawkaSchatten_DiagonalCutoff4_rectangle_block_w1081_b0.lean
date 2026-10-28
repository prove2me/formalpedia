-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1081_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:49:34.945552+00:00
-- url     : https://prove2.me/submissions/90a30498-507f-473a-bc71-60664c3e1901

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
theorem support_rectangle_w1081_s0_0 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14931783/78125000 : ℝ)*x 0 + (6068536573/10000000000 : ℝ)*x 1 + (4772709339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14931783/78125000 : ℝ)^4137 ≤ (443585470991/4000000000000 : ℝ)^3113 := by
    have hnat : (14931783 : ℕ)^4137*4000000000000^3113 ≤ 443585470991^3113*78125000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14931783 78125000 443585470991 4000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6068536573/10000000000 : ℝ)^4137 ≤ (6436369192697/12500000000000 : ℝ)^3113 := by
    have hnat : (6068536573 : ℕ)^4137*12500000000000^3113 ≤ 6436369192697^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6068536573 10000000000 6436369192697 12500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772709339/10000000000 : ℝ)^4137 ≤ (37419409669543/100000000000000 : ℝ)^3113 := by
    have hnat : (4772709339 : ℕ)^4137*100000000000000^3113 ≤ 37419409669543^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772709339 10000000000 37419409669543 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14931783/78125000 : ℝ), (6068536573/10000000000 : ℝ), (4772709339/10000000000 : ℝ)] ![(443585470991/4000000000000 : ℝ), (6436369192697/12500000000000 : ℝ), (37419409669543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14931783/78125000 : ℝ)|^4137 ≤ (443585470991/4000000000000 : ℝ)^3113
        have hw : |(-14931783/78125000 : ℝ)|=(14931783/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6068536573/10000000000 : ℝ)|^4137 ≤ (6436369192697/12500000000000 : ℝ)^3113
        have hw : |(6068536573/10000000000 : ℝ)|=(6068536573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772709339/10000000000 : ℝ)|^4137 ≤ (37419409669543/100000000000000 : ℝ)^3113
        have hw : |(4772709339/10000000000 : ℝ)|=(4772709339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_1 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (552022881/1000000000 : ℝ)*x 0 + (-2656708673/10000000000 : ℝ)*x 1 + (4772709327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552022881/1000000000 : ℝ)^4137 ≤ (22701033765793/50000000000000 : ℝ)^3113 := by
    have hnat : (552022881 : ℕ)^4137*50000000000000^3113 ≤ 22701033765793^3113*1000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552022881 1000000000 22701033765793 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2656708673/10000000000 : ℝ)^4137 ≤ (17178522913991/100000000000000 : ℝ)^3113 := by
    have hnat : (2656708673 : ℕ)^4137*100000000000000^3113 ≤ 17178522913991^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656708673 10000000000 17178522913991 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772709327/10000000000 : ℝ)^4137 ≤ (584678274133/1562500000000 : ℝ)^3113 := by
    have hnat : (4772709327 : ℕ)^4137*1562500000000^3113 ≤ 584678274133^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772709327 10000000000 584678274133 1562500000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(552022881/1000000000 : ℝ), (-2656708673/10000000000 : ℝ), (4772709327/10000000000 : ℝ)] ![(22701033765793/50000000000000 : ℝ), (17178522913991/100000000000000 : ℝ), (584678274133/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(552022881/1000000000 : ℝ)|^4137 ≤ (22701033765793/50000000000000 : ℝ)^3113
        have hw : |(552022881/1000000000 : ℝ)|=(552022881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2656708673/10000000000 : ℝ)|^4137 ≤ (17178522913991/100000000000000 : ℝ)^3113
        have hw : |(-2656708673/10000000000 : ℝ)|=(2656708673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772709327/10000000000 : ℝ)|^4137 ≤ (584678274133/1562500000000 : ℝ)^3113
        have hw : |(4772709327/10000000000 : ℝ)|=(4772709327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_2 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2760114443/5000000000 : ℝ)*x 0 + (1193177331/2500000000 : ℝ)*x 1 + (-2656708579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760114443/5000000000 : ℝ)^4137 ≤ (1816082734491/4000000000000 : ℝ)^3113 := by
    have hnat : (2760114443 : ℕ)^4137*4000000000000^3113 ≤ 1816082734491^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760114443 5000000000 1816082734491 4000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193177331/2500000000 : ℝ)^4137 ≤ (18709704756627/50000000000000 : ℝ)^3113 := by
    have hnat : (1193177331 : ℕ)^4137*50000000000000^3113 ≤ 18709704756627^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193177331 2500000000 18709704756627 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2656708579/10000000000 : ℝ)^4137 ≤ (17178522106243/100000000000000 : ℝ)^3113 := by
    have hnat : (2656708579 : ℕ)^4137*100000000000000^3113 ≤ 17178522106243^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656708579 10000000000 17178522106243 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760114443/5000000000 : ℝ), (1193177331/2500000000 : ℝ), (-2656708579/10000000000 : ℝ)] ![(1816082734491/4000000000000 : ℝ), (18709704756627/50000000000000 : ℝ), (17178522106243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760114443/5000000000 : ℝ)|^4137 ≤ (1816082734491/4000000000000 : ℝ)^3113
        have hw : |(2760114443/5000000000 : ℝ)|=(2760114443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193177331/2500000000 : ℝ)|^4137 ≤ (18709704756627/50000000000000 : ℝ)^3113
        have hw : |(1193177331/2500000000 : ℝ)|=(1193177331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2656708579/10000000000 : ℝ)|^4137 ≤ (17178522106243/100000000000000 : ℝ)^3113
        have hw : |(-2656708579/10000000000 : ℝ)|=(2656708579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_3 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205970503/10000000000 : ℝ)*x 0 + (3124076013/10000000000 : ℝ)*x 1 + (5671281591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205970503/10000000000 : ℝ)^4137 ≤ (15816471405031/50000000000000 : ℝ)^3113 := by
    have hnat : (4205970503 : ℕ)^4137*50000000000000^3113 ≤ 15816471405031^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205970503 10000000000 15816471405031 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124076013/10000000000 : ℝ)^4137 ≤ (21306579039003/100000000000000 : ℝ)^3113 := by
    have hnat : (3124076013 : ℕ)^4137*100000000000000^3113 ≤ 21306579039003^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124076013 10000000000 21306579039003 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671281591/10000000000 : ℝ)^4137 ≤ (941209562691/2000000000000 : ℝ)^3113 := by
    have hnat : (5671281591 : ℕ)^4137*2000000000000^3113 ≤ 941209562691^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671281591 10000000000 941209562691 2000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205970503/10000000000 : ℝ), (3124076013/10000000000 : ℝ), (5671281591/10000000000 : ℝ)] ![(15816471405031/50000000000000 : ℝ), (21306579039003/100000000000000 : ℝ), (941209562691/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205970503/10000000000 : ℝ)|^4137 ≤ (15816471405031/50000000000000 : ℝ)^3113
        have hw : |(4205970503/10000000000 : ℝ)|=(4205970503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124076013/10000000000 : ℝ)|^4137 ≤ (21306579039003/100000000000000 : ℝ)^3113
        have hw : |(3124076013/10000000000 : ℝ)|=(3124076013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671281591/10000000000 : ℝ)|^4137 ≤ (941209562691/2000000000000 : ℝ)^3113
        have hw : |(5671281591/10000000000 : ℝ)|=(5671281591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_4 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191659623/1000000000 : ℝ)*x 0 + (300385199/625000000 : ℝ)*x 1 + (6033911053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191659623/1000000000 : ℝ)^4137 ≤ (5565369519161/50000000000000 : ℝ)^3113 := by
    have hnat : (191659623 : ℕ)^4137*50000000000000^3113 ≤ 5565369519161^3113*1000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191659623 1000000000 5565369519161 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300385199/625000000 : ℝ)^4137 ≤ (37768376373217/100000000000000 : ℝ)^3113 := by
    have hnat : (300385199 : ℕ)^4137*100000000000000^3113 ≤ 37768376373217^3113*625000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300385199 625000000 37768376373217 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033911053/10000000000 : ℝ)^4137 ≤ (1596902643077/3125000000000 : ℝ)^3113 := by
    have hnat : (6033911053 : ℕ)^4137*3125000000000^3113 ≤ 1596902643077^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033911053 10000000000 1596902643077 3125000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191659623/1000000000 : ℝ), (300385199/625000000 : ℝ), (6033911053/10000000000 : ℝ)] ![(5565369519161/50000000000000 : ℝ), (37768376373217/100000000000000 : ℝ), (1596902643077/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191659623/1000000000 : ℝ)|^4137 ≤ (5565369519161/50000000000000 : ℝ)^3113
        have hw : |(-191659623/1000000000 : ℝ)|=(191659623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300385199/625000000 : ℝ)|^4137 ≤ (37768376373217/100000000000000 : ℝ)^3113
        have hw : |(300385199/625000000 : ℝ)|=(300385199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033911053/10000000000 : ℝ)|^4137 ≤ (1596902643077/3125000000000 : ℝ)^3113
        have hw : |(6033911053/10000000000 : ℝ)|=(6033911053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_5 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168439411/10000000000 : ℝ)*x 0 + (-697755067/5000000000 : ℝ)*x 1 + (6033909283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168439411/10000000000 : ℝ)^4137 ≤ (8319571822081/20000000000000 : ℝ)^3113 := by
    have hnat : (5168439411 : ℕ)^4137*20000000000000^3113 ≤ 8319571822081^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168439411 10000000000 8319571822081 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697755067/5000000000 : ℝ)^4137 ≤ (1825319055181/25000000000000 : ℝ)^3113 := by
    have hnat : (697755067 : ℕ)^4137*25000000000000^3113 ≤ 1825319055181^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697755067 5000000000 1825319055181 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033909283/10000000000 : ℝ)^4137 ≤ (10220172931511/20000000000000 : ℝ)^3113 := by
    have hnat : (6033909283 : ℕ)^4137*20000000000000^3113 ≤ 10220172931511^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033909283 10000000000 10220172931511 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168439411/10000000000 : ℝ), (-697755067/5000000000 : ℝ), (6033909283/10000000000 : ℝ)] ![(8319571822081/20000000000000 : ℝ), (1825319055181/25000000000000 : ℝ), (10220172931511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168439411/10000000000 : ℝ)|^4137 ≤ (8319571822081/20000000000000 : ℝ)^3113
        have hw : |(5168439411/10000000000 : ℝ)|=(5168439411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-697755067/5000000000 : ℝ)|^4137 ≤ (1825319055181/25000000000000 : ℝ)^3113
        have hw : |(-697755067/5000000000 : ℝ)|=(697755067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033909283/10000000000 : ℝ)|^4137 ≤ (10220172931511/20000000000000 : ℝ)^3113
        have hw : |(6033909283/10000000000 : ℝ)|=(6033909283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_6 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1292109843/2500000000 : ℝ)*x 0 + (3016955373/5000000000 : ℝ)*x 1 + (-55820313/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292109843/2500000000 : ℝ)^4137 ≤ (2599866168329/6250000000000 : ℝ)^3113 := by
    have hnat : (1292109843 : ℕ)^4137*6250000000000^3113 ≤ 2599866168329^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292109843 2500000000 2599866168329 6250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016955373/5000000000 : ℝ)^4137 ≤ (10220176224651/20000000000000 : ℝ)^3113 := by
    have hnat : (3016955373 : ℕ)^4137*20000000000000^3113 ≤ 10220176224651^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016955373 5000000000 10220176224651 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55820313/400000000 : ℝ)^4137 ≤ (7301260166253/100000000000000 : ℝ)^3113 := by
    have hnat : (55820313 : ℕ)^4137*100000000000000^3113 ≤ 7301260166253^3113*400000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55820313 400000000 7301260166253 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292109843/2500000000 : ℝ), (3016955373/5000000000 : ℝ), (-55820313/400000000 : ℝ)] ![(2599866168329/6250000000000 : ℝ), (10220176224651/20000000000000 : ℝ), (7301260166253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292109843/2500000000 : ℝ)|^4137 ≤ (2599866168329/6250000000000 : ℝ)^3113
        have hw : |(1292109843/2500000000 : ℝ)|=(1292109843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3016955373/5000000000 : ℝ)|^4137 ≤ (10220176224651/20000000000000 : ℝ)^3113
        have hw : |(3016955373/5000000000 : ℝ)|=(3016955373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55820313/400000000 : ℝ)|^4137 ≤ (7301260166253/100000000000000 : ℝ)^3113
        have hw : |(-55820313/400000000 : ℝ)|=(55820313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s0_7 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2108220919/5000000000 : ℝ)*x 0 + (1401379801/2500000000 : ℝ)*x 1 + (3192141191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108220919/5000000000 : ℝ)^4137 ≤ (15868822953161/50000000000000 : ℝ)^3113 := by
    have hnat : (2108220919 : ℕ)^4137*50000000000000^3113 ≤ 15868822953161^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108220919 5000000000 15868822953161 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401379801/2500000000 : ℝ)^4137 ≤ (11584165662533/25000000000000 : ℝ)^3113 := by
    have hnat : (1401379801 : ℕ)^4137*25000000000000^3113 ≤ 11584165662533^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401379801 2500000000 11584165662533 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192141191/10000000000 : ℝ)^4137 ≤ (4385138285389/20000000000000 : ℝ)^3113 := by
    have hnat : (3192141191 : ℕ)^4137*20000000000000^3113 ≤ 4385138285389^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192141191 10000000000 4385138285389 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108220919/5000000000 : ℝ), (1401379801/2500000000 : ℝ), (3192141191/10000000000 : ℝ)] ![(15868822953161/50000000000000 : ℝ), (11584165662533/25000000000000 : ℝ), (4385138285389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108220919/5000000000 : ℝ)|^4137 ≤ (15868822953161/50000000000000 : ℝ)^3113
        have hw : |(2108220919/5000000000 : ℝ)|=(2108220919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401379801/2500000000 : ℝ)|^4137 ≤ (11584165662533/25000000000000 : ℝ)^3113
        have hw : |(1401379801/2500000000 : ℝ)|=(1401379801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192141191/10000000000 : ℝ)|^4137 ≤ (4385138285389/20000000000000 : ℝ)^3113
        have hw : |(3192141191/10000000000 : ℝ)|=(3192141191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1081_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28051/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8273/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8273 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8273*1^2048 ≤ 0^2048*1^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8273/2048 : ℝ) ≤ (617221628034062303/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8273 ≤ (617221628034062303/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8273*25000000000000000000^2048 ≤ 617221628034062303^2048*5^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 617221628034062303 25000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (617221628034062303/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8273 := by
      have hnat : (1 : ℕ)^2048*1^8273 ≤ 1^8273*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25617221628034062303/25000000000000000000 : ℝ) ≤ (2515139550821983/2500000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25617221628034062303/25000000000000000000 : ℝ)^2048 ≤ (2515139550821983/2500000000000000 : ℝ)^8273 := by
      have hnat : (25617221628034062303 : ℕ)^2048*2500000000000000^8273 ≤ 2515139550821983^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25617221628034062303 25000000000000000000 2515139550821983 2500000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515139550821983/2500000000000000 : ℝ)) (X := (25617221628034062303/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13117221628034062303/12500000000000000000 : ℝ) ≤ (1265139550821983/1250000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (13117221628034062303/12500000000000000000 : ℝ)^2048 ≤ (1265139550821983/1250000000000000 : ℝ)^8273 := by
      have hnat : (13117221628034062303 : ℕ)^2048*1250000000000000^8273 ≤ 1265139550821983^8273*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13117221628034062303 12500000000000000000 1265139550821983 1250000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265139550821983/1250000000000000 : ℝ)) (X := (13117221628034062303/12500000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15139550821983/1000000000000000 : ℝ)*(0 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15139550821983/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(617221628034062303/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15139550821983/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8273/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15139550821983/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515139550821983/2500000000000000 : ℝ) by norm_num, show 1+(617221628034062303/25000000000000000000 : ℝ)+(0 : ℝ)=(25617221628034062303/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(617221628034062303/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15139550821983/1000000000000000 : ℝ)*(2/5 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15139550821983/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265139550821983/1250000000000000 : ℝ) by norm_num, show 1+2*(617221628034062303/25000000000000000000 : ℝ)=(13117221628034062303/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15139550821983/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15139550821983/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15139550821983/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15139550821983/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15139550821983/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15139550821983/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14931783/78125000 : ℝ)*X 0 0+(6068536573/10000000000 : ℝ)*X 0 1+(4772709339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((552022881/1000000000 : ℝ)*X 1 0+(-2656708673/10000000000 : ℝ)*X 1 1+(4772709327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760114443/5000000000 : ℝ)*X 2 0+(1193177331/2500000000 : ℝ)*X 2 1+(-2656708579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205970503/10000000000 : ℝ)*X 0 0+(3124076013/10000000000 : ℝ)*X 0 1+(5671281591/10000000000 : ℝ)*X 0 2+(4205970503/10000000000 : ℝ)*X 1 0+(3124076013/10000000000 : ℝ)*X 1 1+(5671281591/10000000000 : ℝ)*X 1 2+(4205970503/10000000000 : ℝ)*X 2 0+(3124076013/10000000000 : ℝ)*X 2 1+(5671281591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-191659623/1000000000 : ℝ)*X 0 0+(300385199/625000000 : ℝ)*X 0 1+(6033911053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168439411/10000000000 : ℝ)*X 1 0+(-697755067/5000000000 : ℝ)*X 1 1+(6033909283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292109843/2500000000 : ℝ)*X 2 0+(3016955373/5000000000 : ℝ)*X 2 1+(-55820313/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108220919/5000000000 : ℝ)*X 0 0+(1401379801/2500000000 : ℝ)*X 0 1+(3192141191/10000000000 : ℝ)*X 0 2+(2108220919/5000000000 : ℝ)*X 1 0+(1401379801/2500000000 : ℝ)*X 1 1+(3192141191/10000000000 : ℝ)*X 1 2+(2108220919/5000000000 : ℝ)*X 2 0+(1401379801/2500000000 : ℝ)*X 2 1+(3192141191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140577623154464544253827/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24128807/100000000000000 : ℝ)*(base1) + (692959887/100000000000000 : ℝ)*(base19) + (648139289/100000000000000 : ℝ)*(base23) + (27722581/50000000000000 : ℝ)*(base24) + (159152249/100000000000000 : ℝ)*(upper3) + (582150344445659/100000000000000 : ℝ)*(major0) + (582150344445659/100000000000000 : ℝ)*(major1) + (582150344445659/100000000000000 : ℝ)*(major2) + (385855042959553/50000000000000 : ℝ)*(sp0) + (6173687042983/800000000000 : ℝ)*(sp1) + (77171086974831/10000000000000 : ℝ)*(sp2) + (196293891803119/50000000000000 : ℝ)*(sp3) + (1511542463/100000000000000 : ℝ)*(sp4) + (121410509/10000000000000 : ℝ)*(sp7) + (49073627730017/12500000000000 : ℝ)*(f.failure) + (385855786666381/50000000000000 : ℝ)*(f.sum) + (63464381121797/50000000000000000000000000000 : ℝ)*base65 + (138705587721797/100000000000000000000000000000 : ℝ)*base67 + (170028205978203/100000000000000000000000000000 : ℝ)*base70 + (31583737721797/100000000000000000000000000000 : ℝ)*base71 + (65508297171797/50000000000000000000000000000 : ℝ)*base73 + (72868728821797/100000000000000000000000000000 : ℝ)*base75 + (402168346721797/100000000000000000000000000000 : ℝ)*base77 + (652055936721797/100000000000000000000000000000 : ℝ)*base79 + (57016841778203/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9053759/1250000000000000000000 : ℝ)*base89 + (9053759/1250000000000000000000 : ℝ)*base91 + (9053759/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (397625006522069863457877/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167131437/10000000000000 : ℝ)*(base19) + (1874786793/100000000000000 : ℝ)*(base23) + (157213/100000000000 : ℝ)*(base39) + (44632933/12500000000000 : ℝ)*(base45) + (161629069/100000000000000 : ℝ)*(upper3) + (358921937/100000000000000 : ℝ)*(upper5) + (38401628456217/6250000000000 : ℝ)*(major0) + (38401628456217/6250000000000 : ℝ)*(major1) + (614425898086473/100000000000000 : ℝ)*(major2) + (33503633/4000000000000 : ℝ)*(sp2) + (814496657261941/100000000000000 : ℝ)*(sp4) + (814494985947571/100000000000000 : ℝ)*(sp5) + (814494102097323/100000000000000 : ℝ)*(sp6) + (207177515520331/50000000000000 : ℝ)*(sp7) + (207177515520331/50000000000000 : ℝ)*(f.failure) + (814496814474941/100000000000000 : ℝ)*(f.sum) + (34093728674213/20000000000000000000000000000 : ℝ)*base66 + (97151355864041/100000000000000000000000000000 : ℝ)*base68 + (14668337850439/6250000000000000000000000000 : ℝ)*base70 + (601919780364041/100000000000000000000000000000 : ℝ)*base72 + (39311187165787/20000000000000000000000000000 : ℝ)*base73 + (18506238899561/6250000000000000000000000000 : ℝ)*base75 + (36145503769189/6250000000000000000000000000 : ℝ)*base78 + (66077812794189/6250000000000000000000000000 : ℝ)*base80 + (2286713205811/3125000000000000000000000000 : ℝ)*base81 + (49350837/5000000000000000000000 : ℝ)*base89 + (49350837/5000000000000000000000 : ℝ)*base91 + (649163/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1081_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1081_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1081_s1_0 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-265040239/1250000000 : ℝ)*x 0 + (5718138527/10000000000 : ℝ)*x 1 + (199569559/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265040239/1250000000 : ℝ)^4137 ≤ (2545987631581/20000000000000 : ℝ)^3113 := by
    have hnat : (265040239 : ℕ)^4137*20000000000000^3113 ≤ 2545987631581^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265040239 1250000000 2545987631581 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5718138527/10000000000 : ℝ)^4137 ≤ (23788949585627/50000000000000 : ℝ)^3113 := by
    have hnat : (5718138527 : ℕ)^4137*50000000000000^3113 ≤ 23788949585627^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718138527 10000000000 23788949585627 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199569559/400000000 : ℝ)^4137 ≤ (39692162652059/100000000000000 : ℝ)^3113 := by
    have hnat : (199569559 : ℕ)^4137*100000000000000^3113 ≤ 39692162652059^3113*400000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199569559 400000000 39692162652059 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265040239/1250000000 : ℝ), (5718138527/10000000000 : ℝ), (199569559/400000000 : ℝ)] ![(2545987631581/20000000000000 : ℝ), (23788949585627/50000000000000 : ℝ), (39692162652059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265040239/1250000000 : ℝ)|^4137 ≤ (2545987631581/20000000000000 : ℝ)^3113
        have hw : |(-265040239/1250000000 : ℝ)|=(265040239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5718138527/10000000000 : ℝ)|^4137 ≤ (23788949585627/50000000000000 : ℝ)^3113
        have hw : |(5718138527/10000000000 : ℝ)|=(5718138527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199569559/400000000 : ℝ)|^4137 ≤ (39692162652059/100000000000000 : ℝ)^3113
        have hw : |(199569559/400000000 : ℝ)|=(199569559/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_1 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422485461/10000000000 : ℝ)*x 0 + (-2514924881/10000000000 : ℝ)*x 1 + (4989239249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422485461/10000000000 : ℝ)^4137 ≤ (8867368919529/20000000000000 : ℝ)^3113 := by
    have hnat : (5422485461 : ℕ)^4137*20000000000000^3113 ≤ 8867368919529^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422485461 10000000000 8867368919529 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514924881/10000000000 : ℝ)^4137 ≤ (798549492059/5000000000000 : ℝ)^3113 := by
    have hnat : (2514924881 : ℕ)^4137*5000000000000^3113 ≤ 798549492059^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514924881 10000000000 798549492059 5000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989239249/10000000000 : ℝ)^4137 ≤ (39692165548919/100000000000000 : ℝ)^3113 := by
    have hnat : (4989239249 : ℕ)^4137*100000000000000^3113 ≤ 39692165548919^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989239249 10000000000 39692165548919 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422485461/10000000000 : ℝ), (-2514924881/10000000000 : ℝ), (4989239249/10000000000 : ℝ)] ![(8867368919529/20000000000000 : ℝ), (798549492059/5000000000000 : ℝ), (39692165548919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422485461/10000000000 : ℝ)|^4137 ≤ (8867368919529/20000000000000 : ℝ)^3113
        have hw : |(5422485461/10000000000 : ℝ)|=(5422485461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2514924881/10000000000 : ℝ)|^4137 ≤ (798549492059/5000000000000 : ℝ)^3113
        have hw : |(-2514924881/10000000000 : ℝ)|=(2514924881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989239249/10000000000 : ℝ)|^4137 ≤ (39692165548919/100000000000000 : ℝ)^3113
        have hw : |(4989239249/10000000000 : ℝ)|=(4989239249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_2 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422486217/10000000000 : ℝ)*x 0 + (4989238443/10000000000 : ℝ)*x 1 + (-628731229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422486217/10000000000 : ℝ)^4137 ≤ (110842132031/250000000000 : ℝ)^3113 := by
    have hnat : (5422486217 : ℕ)^4137*250000000000^3113 ≤ 110842132031^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422486217 10000000000 110842132031 250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989238443/10000000000 : ℝ)^4137 ≤ (15876862811/40000000000 : ℝ)^3113 := by
    have hnat : (4989238443 : ℕ)^4137*40000000000^3113 ≤ 15876862811^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989238443 10000000000 15876862811 40000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628731229/2500000000 : ℝ)^4137 ≤ (199637376707/1250000000000 : ℝ)^3113 := by
    have hnat : (628731229 : ℕ)^4137*1250000000000^3113 ≤ 199637376707^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628731229 2500000000 199637376707 1250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422486217/10000000000 : ℝ), (4989238443/10000000000 : ℝ), (-628731229/2500000000 : ℝ)] ![(110842132031/250000000000 : ℝ), (15876862811/40000000000 : ℝ), (199637376707/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422486217/10000000000 : ℝ)|^4137 ≤ (110842132031/250000000000 : ℝ)^3113
        have hw : |(5422486217/10000000000 : ℝ)|=(5422486217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989238443/10000000000 : ℝ)|^4137 ≤ (15876862811/40000000000 : ℝ)^3113
        have hw : |(4989238443/10000000000 : ℝ)|=(4989238443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-628731229/2500000000 : ℝ)|^4137 ≤ (199637376707/1250000000000 : ℝ)^3113
        have hw : |(-628731229/2500000000 : ℝ)|=(628731229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_3 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161278519/5000000000 : ℝ)*x 0 + (3665430759/10000000000 : ℝ)*x 1 + (5098226099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161278519/5000000000 : ℝ)^4137 ≤ (3280349707519/10000000000000 : ℝ)^3113 := by
    have hnat : (2161278519 : ℕ)^4137*10000000000000^3113 ≤ 3280349707519^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161278519 5000000000 3280349707519 10000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665430759/10000000000 : ℝ)^4137 ≤ (823373634781/3125000000000 : ℝ)^3113 := by
    have hnat : (3665430759 : ℕ)^4137*3125000000000^3113 ≤ 823373634781^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665430759 10000000000 823373634781 3125000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098226099/10000000000 : ℝ)^4137 ≤ (40848546594441/100000000000000 : ℝ)^3113 := by
    have hnat : (5098226099 : ℕ)^4137*100000000000000^3113 ≤ 40848546594441^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098226099 10000000000 40848546594441 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161278519/5000000000 : ℝ), (3665430759/10000000000 : ℝ), (5098226099/10000000000 : ℝ)] ![(3280349707519/10000000000000 : ℝ), (823373634781/3125000000000 : ℝ), (40848546594441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161278519/5000000000 : ℝ)|^4137 ≤ (3280349707519/10000000000000 : ℝ)^3113
        have hw : |(2161278519/5000000000 : ℝ)|=(2161278519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665430759/10000000000 : ℝ)|^4137 ≤ (823373634781/3125000000000 : ℝ)^3113
        have hw : |(3665430759/10000000000 : ℝ)|=(3665430759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098226099/10000000000 : ℝ)|^4137 ≤ (40848546594441/100000000000000 : ℝ)^3113
        have hw : |(5098226099/10000000000 : ℝ)|=(5098226099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_4 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132576309/625000000 : ℝ)*x 0 + (4999424917/10000000000 : ℝ)*x 1 + (2853872123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132576309/625000000 : ℝ)^4137 ≤ (12737111744171/100000000000000 : ℝ)^3113 := by
    have hnat : (132576309 : ℕ)^4137*100000000000000^3113 ≤ 12737111744171^3113*625000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132576309 625000000 12737111744171 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999424917/10000000000 : ℝ)^4137 ≤ (994997236507/2500000000000 : ℝ)^3113 := by
    have hnat : (4999424917 : ℕ)^4137*2500000000000^3113 ≤ 994997236507^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999424917 10000000000 994997236507 2500000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2853872123/5000000000 : ℝ)^4137 ≤ (23731499387197/50000000000000 : ℝ)^3113 := by
    have hnat : (2853872123 : ℕ)^4137*50000000000000^3113 ≤ 23731499387197^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853872123 5000000000 23731499387197 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132576309/625000000 : ℝ), (4999424917/10000000000 : ℝ), (2853872123/5000000000 : ℝ)] ![(12737111744171/100000000000000 : ℝ), (994997236507/2500000000000 : ℝ), (23731499387197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132576309/625000000 : ℝ)|^4137 ≤ (12737111744171/100000000000000 : ℝ)^3113
        have hw : |(-132576309/625000000 : ℝ)|=(132576309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999424917/10000000000 : ℝ)|^4137 ≤ (994997236507/2500000000000 : ℝ)^3113
        have hw : |(4999424917/10000000000 : ℝ)|=(4999424917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2853872123/5000000000 : ℝ)|^4137 ≤ (23731499387197/50000000000000 : ℝ)^3113
        have hw : |(2853872123/5000000000 : ℝ)|=(2853872123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_5 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5236189501/10000000000 : ℝ)*x 0 + (-1796417191/10000000000 : ℝ)*x 1 + (5707746391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236189501/10000000000 : ℝ)^4137 ≤ (42324066087521/100000000000000 : ℝ)^3113 := by
    have hnat : (5236189501 : ℕ)^4137*100000000000000^3113 ≤ 42324066087521^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236189501 10000000000 42324066087521 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796417191/10000000000 : ℝ)^4137 ≤ (5106455710721/50000000000000 : ℝ)^3113 := by
    have hnat : (1796417191 : ℕ)^4137*50000000000000^3113 ≤ 5106455710721^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796417191 10000000000 5106455710721 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707746391/10000000000 : ℝ)^4137 ≤ (9492604495709/20000000000000 : ℝ)^3113 := by
    have hnat : (5707746391 : ℕ)^4137*20000000000000^3113 ≤ 9492604495709^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707746391 10000000000 9492604495709 20000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236189501/10000000000 : ℝ), (-1796417191/10000000000 : ℝ), (5707746391/10000000000 : ℝ)] ![(42324066087521/100000000000000 : ℝ), (5106455710721/50000000000000 : ℝ), (9492604495709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236189501/10000000000 : ℝ)|^4137 ≤ (42324066087521/100000000000000 : ℝ)^3113
        have hw : |(5236189501/10000000000 : ℝ)|=(5236189501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796417191/10000000000 : ℝ)|^4137 ≤ (5106455710721/50000000000000 : ℝ)^3113
        have hw : |(-1796417191/10000000000 : ℝ)|=(1796417191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707746391/10000000000 : ℝ)|^4137 ≤ (9492604495709/20000000000000 : ℝ)^3113
        have hw : |(5707746391/10000000000 : ℝ)|=(5707746391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_6 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047237483/2000000000 : ℝ)*x 0 + (2853874359/5000000000 : ℝ)*x 1 + (-898208377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047237483/2000000000 : ℝ)^4137 ≤ (42324043680057/100000000000000 : ℝ)^3113 := by
    have hnat : (1047237483 : ℕ)^4137*100000000000000^3113 ≤ 42324043680057^3113*2000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047237483 2000000000 42324043680057 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2853874359/5000000000 : ℝ)^4137 ≤ (47463048193959/100000000000000 : ℝ)^3113 := by
    have hnat : (2853874359 : ℕ)^4137*100000000000000^3113 ≤ 47463048193959^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853874359 5000000000 47463048193959 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898208377/5000000000 : ℝ)^4137 ≤ (10212908119799/100000000000000 : ℝ)^3113 := by
    have hnat : (898208377 : ℕ)^4137*100000000000000^3113 ≤ 10212908119799^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898208377 5000000000 10212908119799 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047237483/2000000000 : ℝ), (2853874359/5000000000 : ℝ), (-898208377/5000000000 : ℝ)] ![(42324043680057/100000000000000 : ℝ), (47463048193959/100000000000000 : ℝ), (10212908119799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047237483/2000000000 : ℝ)|^4137 ≤ (42324043680057/100000000000000 : ℝ)^3113
        have hw : |(1047237483/2000000000 : ℝ)|=(1047237483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2853874359/5000000000 : ℝ)|^4137 ≤ (47463048193959/100000000000000 : ℝ)^3113
        have hw : |(2853874359/5000000000 : ℝ)|=(2853874359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898208377/5000000000 : ℝ)|^4137 ≤ (10212908119799/100000000000000 : ℝ)^3113
        have hw : |(-898208377/5000000000 : ℝ)|=(898208377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s1_7 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162159737/5000000000 : ℝ)*x 0 + (20312801/40000000 : ℝ)*x 1 + (1842929243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162159737/5000000000 : ℝ)^4137 ≤ (16410636419843/50000000000000 : ℝ)^3113 := by
    have hnat : (2162159737 : ℕ)^4137*50000000000000^3113 ≤ 16410636419843^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162159737 5000000000 16410636419843 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20312801/40000000 : ℝ)^4137 ≤ (20317725629631/50000000000000 : ℝ)^3113 := by
    have hnat : (20312801 : ℕ)^4137*50000000000000^3113 ≤ 20317725629631^3113*40000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20312801 40000000 20317725629631 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842929243/5000000000 : ℝ)^4137 ≤ (26543275884561/100000000000000 : ℝ)^3113 := by
    have hnat : (1842929243 : ℕ)^4137*100000000000000^3113 ≤ 26543275884561^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842929243 5000000000 26543275884561 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162159737/5000000000 : ℝ), (20312801/40000000 : ℝ), (1842929243/5000000000 : ℝ)] ![(16410636419843/50000000000000 : ℝ), (20317725629631/50000000000000 : ℝ), (26543275884561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162159737/5000000000 : ℝ)|^4137 ≤ (16410636419843/50000000000000 : ℝ)^3113
        have hw : |(2162159737/5000000000 : ℝ)|=(2162159737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20312801/40000000 : ℝ)|^4137 ≤ (20317725629631/50000000000000 : ℝ)^3113
        have hw : |(20312801/40000000 : ℝ)|=(20312801/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842929243/5000000000 : ℝ)|^4137 ≤ (26543275884561/100000000000000 : ℝ)^3113
        have hw : |(1842929243/5000000000 : ℝ)|=(1842929243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1081_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/625 : ℝ)*pair X i i ≤ pair X i h) :
    (5301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (259/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/625 : ℝ) ^ (8273/2048 : ℝ) ≤ (254021629/50000000000000000000 : ℝ) := by
    have hpowers : (1/625 : ℝ)^8273 ≤ (254021629/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1 : ℕ)^8273*50000000000000000000^2048 ≤ 254021629^2048*625^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 625 254021629 50000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/625 : ℝ)) (X := (254021629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28051/100000 : ℝ) ^ (8273/2048 : ℝ) ≤ (58878849957917101/10000000000000000000 : ℝ) := by
    have hpowers : (28051/100000 : ℝ)^8273 ≤ (58878849957917101/10000000000000000000 : ℝ)^2048 := by
      have hnat : (28051 : ℕ)^8273*10000000000000000000^2048 ≤ 58878849957917101^2048*100000^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28051 100000 58878849957917101 10000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28051/100000 : ℝ)) (X := (58878849957917101/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000254021629/25000000000000000000 : ℝ) ≤ (5000000000012577/5000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25000000000254021629/25000000000000000000 : ℝ)^2048 ≤ (5000000000012577/5000000000000000 : ℝ)^8273 := by
      have hnat : (25000000000254021629 : ℕ)^2048*5000000000000000^8273 ≤ 5000000000012577^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000254021629 25000000000000000000 5000000000012577 5000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000012577/5000000000000000 : ℝ)) (X := (25000000000254021629/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25147197125021803567/25000000000000000000 : ℝ) ≤ (10014543416763219/10000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25147197125021803567/25000000000000000000 : ℝ)^2048 ≤ (10014543416763219/10000000000000000 : ℝ)^8273 := by
      have hnat : (25147197125021803567 : ℕ)^2048*10000000000000000^8273 ≤ 10014543416763219^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25147197125021803567 25000000000000000000 10014543416763219 10000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014543416763219/10000000000000000 : ℝ)) (X := (25147197125021803567/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5058878849957917101/5000000000000000000 : ℝ) ≤ (2507271708375321/2500000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (5058878849957917101/5000000000000000000 : ℝ)^2048 ≤ (2507271708375321/2500000000000000 : ℝ)^8273 := by
      have hnat : (5058878849957917101 : ℕ)^2048*2500000000000000^8273 ≤ 2507271708375321^8273*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5058878849957917101 5000000000000000000 2507271708375321 2500000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507271708375321/2500000000000000 : ℝ)) (X := (5058878849957917101/5000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(254021629/50000000000000000000 : ℝ) ≤ ((46484224351224231569/46485000000000000000 : ℝ)+2*(969561115871/185940000000000 : ℝ)*(1/625 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (46484224351224231569/46485000000000000000 : ℝ)+2*(969561115871/185940000000000 : ℝ)*(1/625 : ℝ)=(5000000000012577/5000000000000000 : ℝ) by norm_num, show 1+2*(254021629/50000000000000000000 : ℝ)=(25000000000254021629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58878849957917101/10000000000000000000 : ℝ)+(254021629/50000000000000000000 : ℝ) ≤ ((46484224351224231569/46485000000000000000 : ℝ)+(969561115871/185940000000000 : ℝ)*((28051/100000 : ℝ)+(1/625 : ℝ)))^(8273/2048 : ℝ) := by
    rw [show (46484224351224231569/46485000000000000000 : ℝ)+(969561115871/185940000000000 : ℝ)*((28051/100000 : ℝ)+(1/625 : ℝ))=(10014543416763219/10000000000000000 : ℝ) by norm_num, show 1+(58878849957917101/10000000000000000000 : ℝ)+(254021629/50000000000000000000 : ℝ)=(25147197125021803567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58878849957917101/10000000000000000000 : ℝ) ≤ ((46484224351224231569/46485000000000000000 : ℝ)+2*(969561115871/185940000000000 : ℝ)*(28051/100000 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (46484224351224231569/46485000000000000000 : ℝ)+2*(969561115871/185940000000000 : ℝ)*(28051/100000 : ℝ)=(2507271708375321/2500000000000000 : ℝ) by norm_num, show 1+2*(58878849957917101/10000000000000000000 : ℝ)=(5058878849957917101/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46484224351224231569/46485000000000000000 : ℝ)*(X 1 0+X 2 0)+(969561115871/185940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1/625 : ℝ)) (hi := (28051/100000 : ℝ)) (c := (46484224351224231569/46485000000000000000 : ℝ)) (alpha := (969561115871/185940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46484224351224231569/46485000000000000000 : ℝ)*(X 0 1+X 2 1)+(969561115871/185940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1/625 : ℝ)) (hi := (28051/100000 : ℝ)) (c := (46484224351224231569/46485000000000000000 : ℝ)) (alpha := (969561115871/185940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46484224351224231569/46485000000000000000 : ℝ)*(X 0 2+X 1 2)+(969561115871/185940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (1/625 : ℝ)) (hi := (28051/100000 : ℝ)) (c := (46484224351224231569/46485000000000000000 : ℝ)) (alpha := (969561115871/185940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-265040239/1250000000 : ℝ)*X 0 0+(5718138527/10000000000 : ℝ)*X 0 1+(199569559/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422485461/10000000000 : ℝ)*X 1 0+(-2514924881/10000000000 : ℝ)*X 1 1+(4989239249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5422486217/10000000000 : ℝ)*X 2 0+(4989238443/10000000000 : ℝ)*X 2 1+(-628731229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161278519/5000000000 : ℝ)*X 0 0+(3665430759/10000000000 : ℝ)*X 0 1+(5098226099/10000000000 : ℝ)*X 0 2+(2161278519/5000000000 : ℝ)*X 1 0+(3665430759/10000000000 : ℝ)*X 1 1+(5098226099/10000000000 : ℝ)*X 1 2+(2161278519/5000000000 : ℝ)*X 2 0+(3665430759/10000000000 : ℝ)*X 2 1+(5098226099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132576309/625000000 : ℝ)*X 0 0+(4999424917/10000000000 : ℝ)*X 0 1+(2853872123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236189501/10000000000 : ℝ)*X 1 0+(-1796417191/10000000000 : ℝ)*X 1 1+(5707746391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047237483/2000000000 : ℝ)*X 2 0+(2853874359/5000000000 : ℝ)*X 2 1+(-898208377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162159737/5000000000 : ℝ)*X 0 0+(20312801/40000000 : ℝ)*X 0 1+(1842929243/5000000000 : ℝ)*X 0 2+(2162159737/5000000000 : ℝ)*X 1 0+(20312801/40000000 : ℝ)*X 1 1+(1842929243/5000000000 : ℝ)*X 1 2+(2162159737/5000000000 : ℝ)*X 2 0+(20312801/40000000 : ℝ)*X 2 1+(1842929243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131182878270765110550092379/25825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32077557/25000000000000 : ℝ)*(base1) + (104180541/10000000000000 : ℝ)*(base19) + (246616113/20000000000000 : ℝ)*(base23) + (45437863/50000000000000 : ℝ)*(upper3) + (65290469/50000000000000 : ℝ)*(upper5) + (206988252205473/20000000000000 : ℝ)*(major0) + (206988252205473/20000000000000 : ℝ)*(major1) + (206988252205473/20000000000000 : ℝ)*(major2) + (685967938037899/50000000000000 : ℝ)*(sp0) + (274388067759117/20000000000000 : ℝ)*(sp1) + (1371940147520429/100000000000000 : ℝ)*(sp2) + (697938569738267/100000000000000 : ℝ)*(sp3) + (176026107/3125000000000 : ℝ)*(sp4) + (142130149/6250000000000 : ℝ)*(sp7) + (2181065537909/312500000000 : ℝ)*(f.failure) + (685970690300497/50000000000000 : ℝ)*(f.sum) + (5925934229/206600000000000000000000000 : ℝ)*base65 + (449568053121219207/103300000000000000000000000000000 : ℝ)*base68 + (138744386254419207/103300000000000000000000000000000 : ℝ)*base70 + (424148902293219207/103300000000000000000000000000000 : ℝ)*base72 + (3293518042409/1033000000000000000000000000 : ℝ)*base74 + (1030545507780719207/103300000000000000000000000000000 : ℝ)*base76 + (327556936539619207/103300000000000000000000000000000 : ℝ)*base78 + (38759692691880793/103300000000000000000000000000000 : ℝ)*base79 + (1510264508817/516500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (235143/31250000000000000000 : ℝ)*base89 + (235143/31250000000000000000 : ℝ)*base91 + (235143/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111709607477411887623649123/38737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2660879851/100000000000000 : ℝ)*(base19) + (672914929/25000000000000 : ℝ)*(base23) + (275392087/100000000000000 : ℝ)*(upper2) + (11690067/2500000000000 : ℝ)*(upper3) + (551042489/100000000000000 : ℝ)*(upper5) + (53250109048567/5000000000000 : ℝ)*(major0) + (53250109048567/5000000000000 : ℝ)*(major1) + (53250109048567/5000000000000 : ℝ)*(major2) + (6801209913/50000000000000 : ℝ)*(sp1) + (619717217/4000000000000 : ℝ)*(sp2) + (705895444684289/50000000000000 : ℝ)*(sp4) + (1411774626068901/100000000000000 : ℝ)*(sp5) + (705886352389219/50000000000000 : ℝ)*(sp6) + (718213376448801/100000000000000 : ℝ)*(sp7) + (718213376448801/100000000000000 : ℝ)*(f.failure) + (705895444684289/50000000000000 : ℝ)*(f.sum) + (25387282152833/4648500000000000000000000000 : ℝ)*base65 + (1522389867309438377/232425000000000000000000000000000 : ℝ)*base68 + (852896200595411623/232425000000000000000000000000000 : ℝ)*base69 + (648122480471936623/232425000000000000000000000000000 : ℝ)*base71 + (12756533621599/9297000000000000000000000000 : ℝ)*base73 + (960561459948813377/232425000000000000000000000000000 : ℝ)*base76 + (908997606002463377/232425000000000000000000000000000 : ℝ)*base78 + (2417879866776963377/232425000000000000000000000000000 : ℝ)*base80 + (36529259289071/4648500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24477473/10000000000000000000000 : ℝ)*base90 + (24477473/10000000000000000000000 : ℝ)*base92 + (24477473/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1081_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (259/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1081_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1081_s2_0 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-544225323/2500000000 : ℝ)*x 0 + (2761414647/5000000000 : ℝ)*x 1 + (2574317683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544225323/2500000000 : ℝ)^4137 ≤ (3295834076339/25000000000000 : ℝ)^3113 := by
    have hnat : (544225323 : ℕ)^4137*25000000000000^3113 ≤ 3295834076339^3113*2500000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544225323 2500000000 3295834076339 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761414647/5000000000 : ℝ)^4137 ≤ (4543049333717/10000000000000 : ℝ)^3113 := by
    have hnat : (2761414647 : ℕ)^4137*10000000000000^3113 ≤ 4543049333717^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761414647 5000000000 4543049333717 10000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574317683/5000000000 : ℝ)^4137 ≤ (41386170331983/100000000000000 : ℝ)^3113 := by
    have hnat : (2574317683 : ℕ)^4137*100000000000000^3113 ≤ 41386170331983^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574317683 5000000000 41386170331983 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544225323/2500000000 : ℝ), (2761414647/5000000000 : ℝ), (2574317683/5000000000 : ℝ)] ![(3295834076339/25000000000000 : ℝ), (4543049333717/10000000000000 : ℝ), (41386170331983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544225323/2500000000 : ℝ)|^4137 ≤ (3295834076339/25000000000000 : ℝ)^3113
        have hw : |(-544225323/2500000000 : ℝ)|=(544225323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761414647/5000000000 : ℝ)|^4137 ≤ (4543049333717/10000000000000 : ℝ)^3113
        have hw : |(2761414647/5000000000 : ℝ)|=(2761414647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574317683/5000000000 : ℝ)|^4137 ≤ (41386170331983/100000000000000 : ℝ)^3113
        have hw : |(2574317683/5000000000 : ℝ)|=(2574317683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_1 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376534371/10000000000 : ℝ)*x 0 + (-1185962809/5000000000 : ℝ)*x 1 + (514863587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376534371/10000000000 : ℝ)^4137 ≤ (43838233746899/100000000000000 : ℝ)^3113 := by
    have hnat : (5376534371 : ℕ)^4137*100000000000000^3113 ≤ 43838233746899^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376534371 10000000000 43838233746899 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185962809/5000000000 : ℝ)^4137 ≤ (295511810523/2000000000000 : ℝ)^3113 := by
    have hnat : (1185962809 : ℕ)^4137*2000000000000^3113 ≤ 295511810523^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185962809 5000000000 295511810523 2000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514863587/1000000000 : ℝ)^4137 ≤ (41386175715921/100000000000000 : ℝ)^3113 := by
    have hnat : (514863587 : ℕ)^4137*100000000000000^3113 ≤ 41386175715921^3113*1000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514863587 1000000000 41386175715921 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376534371/10000000000 : ℝ), (-1185962809/5000000000 : ℝ), (514863587/1000000000 : ℝ)] ![(43838233746899/100000000000000 : ℝ), (295511810523/2000000000000 : ℝ), (41386175715921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376534371/10000000000 : ℝ)|^4137 ≤ (43838233746899/100000000000000 : ℝ)^3113
        have hw : |(5376534371/10000000000 : ℝ)|=(5376534371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1185962809/5000000000 : ℝ)|^4137 ≤ (295511810523/2000000000000 : ℝ)^3113
        have hw : |(-1185962809/5000000000 : ℝ)|=(1185962809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514863587/1000000000 : ℝ)|^4137 ≤ (41386175715921/100000000000000 : ℝ)^3113
        have hw : |(514863587/1000000000 : ℝ)|=(514863587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_2 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376534529/10000000000 : ℝ)*x 0 + (5148635697/10000000000 : ℝ)*x 1 + (-2371925633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376534529/10000000000 : ℝ)^4137 ≤ (43838235458939/100000000000000 : ℝ)^3113 := by
    have hnat : (5376534529 : ℕ)^4137*100000000000000^3113 ≤ 43838235458939^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376534529 10000000000 43838235458939 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5148635697/10000000000 : ℝ)^4137 ≤ (20693086933931/50000000000000 : ℝ)^3113 := by
    have hnat : (5148635697 : ℕ)^4137*50000000000000^3113 ≤ 20693086933931^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148635697 10000000000 20693086933931 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371925633/10000000000 : ℝ)^4137 ≤ (14775590650327/100000000000000 : ℝ)^3113 := by
    have hnat : (2371925633 : ℕ)^4137*100000000000000^3113 ≤ 14775590650327^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371925633 10000000000 14775590650327 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376534529/10000000000 : ℝ), (5148635697/10000000000 : ℝ), (-2371925633/10000000000 : ℝ)] ![(43838235458939/100000000000000 : ℝ), (20693086933931/50000000000000 : ℝ), (14775590650327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376534529/10000000000 : ℝ)|^4137 ≤ (43838235458939/100000000000000 : ℝ)^3113
        have hw : |(5376534529/10000000000 : ℝ)|=(5376534529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5148635697/10000000000 : ℝ)|^4137 ≤ (20693086933931/50000000000000 : ℝ)^3113
        have hw : |(5148635697/10000000000 : ℝ)|=(5148635697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2371925633/10000000000 : ℝ)|^4137 ≤ (14775590650327/100000000000000 : ℝ)^3113
        have hw : |(-2371925633/10000000000 : ℝ)|=(2371925633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_3 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361205653/10000000000 : ℝ)*x 0 + (125281681/312500000 : ℝ)*x 1 + (9266729/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361205653/10000000000 : ℝ)^4137 ≤ (16596924653111/50000000000000 : ℝ)^3113 := by
    have hnat : (4361205653 : ℕ)^4137*50000000000000^3113 ≤ 16596924653111^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361205653 10000000000 16596924653111 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125281681/312500000 : ℝ)^4137 ≤ (14839848913461/50000000000000 : ℝ)^3113 := by
    have hnat : (125281681 : ℕ)^4137*50000000000000^3113 ≤ 14839848913461^3113*312500000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125281681 312500000 14839848913461 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9266729/19531250 : ℝ)^4137 ≤ (37126452857287/100000000000000 : ℝ)^3113 := by
    have hnat : (9266729 : ℕ)^4137*100000000000000^3113 ≤ 37126452857287^3113*19531250^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9266729 19531250 37126452857287 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361205653/10000000000 : ℝ), (125281681/312500000 : ℝ), (9266729/19531250 : ℝ)] ![(16596924653111/50000000000000 : ℝ), (14839848913461/50000000000000 : ℝ), (37126452857287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361205653/10000000000 : ℝ)|^4137 ≤ (16596924653111/50000000000000 : ℝ)^3113
        have hw : |(4361205653/10000000000 : ℝ)|=(4361205653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125281681/312500000 : ℝ)|^4137 ≤ (14839848913461/50000000000000 : ℝ)^3113
        have hw : |(125281681/312500000 : ℝ)|=(125281681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9266729/19531250 : ℝ)|^4137 ≤ (37126452857287/100000000000000 : ℝ)^3113
        have hw : |(9266729/19531250 : ℝ)|=(9266729/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_4 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088511127/5000000000 : ℝ)*x 0 + (515132871/1000000000 : ℝ)*x 1 + (690013487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088511127/5000000000 : ℝ)^4137 ≤ (824019364231/6250000000000 : ℝ)^3113 := by
    have hnat : (1088511127 : ℕ)^4137*6250000000000^3113 ≤ 824019364231^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088511127 5000000000 824019364231 6250000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515132871/1000000000 : ℝ)^4137 ≤ (4141494422943/10000000000000 : ℝ)^3113 := by
    have hnat : (515132871 : ℕ)^4137*10000000000000^3113 ≤ 4141494422943^3113*1000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515132871 1000000000 4141494422943 10000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690013487/1250000000 : ℝ)^4137 ≤ (45400745931753/100000000000000 : ℝ)^3113 := by
    have hnat : (690013487 : ℕ)^4137*100000000000000^3113 ≤ 45400745931753^3113*1250000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690013487 1250000000 45400745931753 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088511127/5000000000 : ℝ), (515132871/1000000000 : ℝ), (690013487/1250000000 : ℝ)] ![(824019364231/6250000000000 : ℝ), (4141494422943/10000000000000 : ℝ), (45400745931753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088511127/5000000000 : ℝ)|^4137 ≤ (824019364231/6250000000000 : ℝ)^3113
        have hw : |(-1088511127/5000000000 : ℝ)|=(1088511127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515132871/1000000000 : ℝ)|^4137 ≤ (4141494422943/10000000000000 : ℝ)^3113
        have hw : |(515132871/1000000000 : ℝ)|=(515132871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690013487/1250000000 : ℝ)|^4137 ≤ (45400745931753/100000000000000 : ℝ)^3113
        have hw : |(690013487/1250000000 : ℝ)|=(690013487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_5 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5281984849/10000000000 : ℝ)*x 0 + (-2000453509/10000000000 : ℝ)*x 1 + (5520107991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281984849/10000000000 : ℝ)^4137 ≤ (21408349169761/50000000000000 : ℝ)^3113 := by
    have hnat : (5281984849 : ℕ)^4137*50000000000000^3113 ≤ 21408349169761^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281984849 10000000000 21408349169761 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000453509/10000000000 : ℝ)^4137 ≤ (5891277336561/50000000000000 : ℝ)^3113 := by
    have hnat : (2000453509 : ℕ)^4137*50000000000000^3113 ≤ 5891277336561^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000453509 10000000000 5891277336561 50000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520107991/10000000000 : ℝ)^4137 ≤ (45400746970107/100000000000000 : ℝ)^3113 := by
    have hnat : (5520107991 : ℕ)^4137*100000000000000^3113 ≤ 45400746970107^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520107991 10000000000 45400746970107 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281984849/10000000000 : ℝ), (-2000453509/10000000000 : ℝ), (5520107991/10000000000 : ℝ)] ![(21408349169761/50000000000000 : ℝ), (5891277336561/50000000000000 : ℝ), (45400746970107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281984849/10000000000 : ℝ)|^4137 ≤ (21408349169761/50000000000000 : ℝ)^3113
        have hw : |(5281984849/10000000000 : ℝ)|=(5281984849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000453509/10000000000 : ℝ)|^4137 ≤ (5891277336561/50000000000000 : ℝ)^3113
        have hw : |(-2000453509/10000000000 : ℝ)|=(2000453509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520107991/10000000000 : ℝ)|^4137 ≤ (45400746970107/100000000000000 : ℝ)^3113
        have hw : |(5520107991/10000000000 : ℝ)|=(5520107991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_6 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640992543/5000000000 : ℝ)*x 0 + (5520107837/10000000000 : ℝ)*x 1 + (-1000226699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640992543/5000000000 : ℝ)^4137 ≤ (42816700892639/100000000000000 : ℝ)^3113 := by
    have hnat : (2640992543 : ℕ)^4137*100000000000000^3113 ≤ 42816700892639^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640992543 5000000000 42816700892639 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520107837/10000000000 : ℝ)^4137 ≤ (283754658043/625000000000 : ℝ)^3113 := by
    have hnat : (5520107837 : ℕ)^4137*625000000000^3113 ≤ 283754658043^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520107837 10000000000 283754658043 625000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000226699/5000000000 : ℝ)^4137 ≤ (11782553804281/100000000000000 : ℝ)^3113 := by
    have hnat : (1000226699 : ℕ)^4137*100000000000000^3113 ≤ 11782553804281^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000226699 5000000000 11782553804281 100000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640992543/5000000000 : ℝ), (5520107837/10000000000 : ℝ), (-1000226699/5000000000 : ℝ)] ![(42816700892639/100000000000000 : ℝ), (283754658043/625000000000 : ℝ), (11782553804281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640992543/5000000000 : ℝ)|^4137 ≤ (42816700892639/100000000000000 : ℝ)^3113
        have hw : |(2640992543/5000000000 : ℝ)|=(2640992543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520107837/10000000000 : ℝ)|^4137 ≤ (283754658043/625000000000 : ℝ)^3113
        have hw : |(5520107837/10000000000 : ℝ)|=(5520107837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000226699/5000000000 : ℝ)|^4137 ≤ (11782553804281/100000000000000 : ℝ)^3113
        have hw : |(-1000226699/5000000000 : ℝ)|=(1000226699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1081_s2_7 (p : ℝ) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2180721789/5000000000 : ℝ)*x 0 + (4739271481/10000000000 : ℝ)*x 1 + (2007181183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180721789/5000000000 : ℝ)^4137 ≤ (1037382996639/3125000000000 : ℝ)^3113 := by
    have hnat : (2180721789 : ℕ)^4137*3125000000000^3113 ≤ 1037382996639^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180721789 5000000000 1037382996639 3125000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4739271481/10000000000 : ℝ)^4137 ≤ (9267853210929/25000000000000 : ℝ)^3113 := by
    have hnat : (4739271481 : ℕ)^4137*25000000000000^3113 ≤ 9267853210929^3113*10000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4739271481 10000000000 9267853210929 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007181183/5000000000 : ℝ)^4137 ≤ (7433082811751/25000000000000 : ℝ)^3113 := by
    have hnat : (2007181183 : ℕ)^4137*25000000000000^3113 ≤ 7433082811751^3113*5000000000^4137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007181183 5000000000 7433082811751 25000000000000 4137 3113 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4137/1024 : ℝ)) 4137 3113 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180721789/5000000000 : ℝ), (4739271481/10000000000 : ℝ), (2007181183/5000000000 : ℝ)] ![(1037382996639/3125000000000 : ℝ), (9267853210929/25000000000000 : ℝ), (7433082811751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180721789/5000000000 : ℝ)|^4137 ≤ (1037382996639/3125000000000 : ℝ)^3113
        have hw : |(2180721789/5000000000 : ℝ)|=(2180721789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4739271481/10000000000 : ℝ)|^4137 ≤ (9267853210929/25000000000000 : ℝ)^3113
        have hw : |(4739271481/10000000000 : ℝ)|=(4739271481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007181183/5000000000 : ℝ)|^4137 ≤ (7433082811751/25000000000000 : ℝ)^3113
        have hw : |(2007181183/5000000000 : ℝ)|=(2007181183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1081_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (259/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1757/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4173/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (259/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (259/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (259/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (259/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (259/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (259/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5301/100000 : ℝ) ^ (8273/2048 : ℝ) ≤ (351518815217217/50000000000000000000 : ℝ) := by
    have hpowers : (5301/100000 : ℝ)^8273 ≤ (351518815217217/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5301 : ℕ)^8273*50000000000000000000^2048 ≤ 351518815217217^2048*100000^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5301 100000 351518815217217 50000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5301/100000 : ℝ)) (X := (351518815217217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (259/1250 : ℝ) ^ (8273/2048 : ℝ) ≤ (173189550434197723/100000000000000000000 : ℝ) := by
    have hpowers : (259/1250 : ℝ)^8273 ≤ (173189550434197723/100000000000000000000 : ℝ)^2048 := by
      have hnat : (259 : ℕ)^8273*100000000000000000000^2048 ≤ 173189550434197723^2048*1250^8273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        259 1250 173189550434197723 100000000000000000000 8273 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (259/1250 : ℝ)) (X := (173189550434197723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000351518815217217/25000000000000000000 : ℝ) ≤ (5000017403764663/5000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (25000351518815217217/25000000000000000000 : ℝ)^2048 ≤ (5000017403764663/5000000000000000 : ℝ)^8273 := by
      have hnat : (25000351518815217217 : ℕ)^2048*5000000000000000^8273 ≤ 5000017403764663^8273*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000351518815217217 25000000000000000000 5000017403764663 5000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000017403764663/5000000000000000 : ℝ)) (X := (25000351518815217217/25000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100173892588064632157/100000000000000000000 : ℝ) ≤ (625268871076187/625000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (100173892588064632157/100000000000000000000 : ℝ)^2048 ≤ (625268871076187/625000000000000 : ℝ)^8273 := by
      have hnat : (100173892588064632157 : ℕ)^2048*625000000000000^8273 ≤ 625268871076187^8273*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100173892588064632157 100000000000000000000 625268871076187 625000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625268871076187/625000000000000 : ℝ)) (X := (100173892588064632157/100000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50173189550434197723/50000000000000000000 : ℝ) ≤ (5004284533454329/5000000000000000 : ℝ) ^ (8273/2048 : ℝ) := by
    have hpowers : (50173189550434197723/50000000000000000000 : ℝ)^2048 ≤ (5004284533454329/5000000000000000 : ℝ)^8273 := by
      have hnat : (50173189550434197723 : ℕ)^2048*5000000000000000^8273 ≤ 5004284533454329^8273*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50173189550434197723 50000000000000000000 5004284533454329 5000000000000000 2048 8273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004284533454329/5000000000000000 : ℝ)) (X := (50173189550434197723/50000000000000000000 : ℝ)) (by norm_num) 8273 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(351518815217217/50000000000000000000 : ℝ) ≤ ((77072648294162419331/77095000000000000000 : ℝ)+2*(2133564844833/770950000000000 : ℝ)*(5301/100000 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (77072648294162419331/77095000000000000000 : ℝ)+2*(2133564844833/770950000000000 : ℝ)*(5301/100000 : ℝ)=(5000017403764663/5000000000000000 : ℝ) by norm_num, show 1+2*(351518815217217/50000000000000000000 : ℝ)=(25000351518815217217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(173189550434197723/100000000000000000000 : ℝ)+(351518815217217/50000000000000000000 : ℝ) ≤ ((77072648294162419331/77095000000000000000 : ℝ)+(2133564844833/770950000000000 : ℝ)*((259/1250 : ℝ)+(5301/100000 : ℝ)))^(8273/2048 : ℝ) := by
    rw [show (77072648294162419331/77095000000000000000 : ℝ)+(2133564844833/770950000000000 : ℝ)*((259/1250 : ℝ)+(5301/100000 : ℝ))=(625268871076187/625000000000000 : ℝ) by norm_num, show 1+(173189550434197723/100000000000000000000 : ℝ)+(351518815217217/50000000000000000000 : ℝ)=(100173892588064632157/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(173189550434197723/100000000000000000000 : ℝ) ≤ ((77072648294162419331/77095000000000000000 : ℝ)+2*(2133564844833/770950000000000 : ℝ)*(259/1250 : ℝ))^(8273/2048 : ℝ) := by
    rw [show (77072648294162419331/77095000000000000000 : ℝ)+2*(2133564844833/770950000000000 : ℝ)*(259/1250 : ℝ)=(5004284533454329/5000000000000000 : ℝ) by norm_num, show 1+2*(173189550434197723/100000000000000000000 : ℝ)=(50173189550434197723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77072648294162419331/77095000000000000000 : ℝ)*(X 1 0+X 2 0)+(2133564844833/770950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (5301/100000 : ℝ)) (hi := (259/1250 : ℝ)) (c := (77072648294162419331/77095000000000000000 : ℝ)) (alpha := (2133564844833/770950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77072648294162419331/77095000000000000000 : ℝ)*(X 0 1+X 2 1)+(2133564844833/770950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (5301/100000 : ℝ)) (hi := (259/1250 : ℝ)) (c := (77072648294162419331/77095000000000000000 : ℝ)) (alpha := (2133564844833/770950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77072648294162419331/77095000000000000000 : ℝ)*(X 0 2+X 1 2)+(2133564844833/770950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8273/2048 : ℝ)) (lo := (5301/100000 : ℝ)) (hi := (259/1250 : ℝ)) (c := (77072648294162419331/77095000000000000000 : ℝ)) (alpha := (2133564844833/770950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-544225323/2500000000 : ℝ)*X 0 0+(2761414647/5000000000 : ℝ)*X 0 1+(2574317683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376534371/10000000000 : ℝ)*X 1 0+(-1185962809/5000000000 : ℝ)*X 1 1+(514863587/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376534529/10000000000 : ℝ)*X 2 0+(5148635697/10000000000 : ℝ)*X 2 1+(-2371925633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361205653/10000000000 : ℝ)*X 0 0+(125281681/312500000 : ℝ)*X 0 1+(9266729/19531250 : ℝ)*X 0 2+(4361205653/10000000000 : ℝ)*X 1 0+(125281681/312500000 : ℝ)*X 1 1+(9266729/19531250 : ℝ)*X 1 2+(4361205653/10000000000 : ℝ)*X 2 0+(125281681/312500000 : ℝ)*X 2 1+(9266729/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088511127/5000000000 : ℝ)*X 0 0+(515132871/1000000000 : ℝ)*X 0 1+(690013487/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281984849/10000000000 : ℝ)*X 1 0+(-2000453509/10000000000 : ℝ)*X 1 1+(5520107991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640992543/5000000000 : ℝ)*X 2 0+(5520107837/10000000000 : ℝ)*X 2 1+(-1000226699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180721789/5000000000 : ℝ)*X 0 0+(4739271481/10000000000 : ℝ)*X 0 1+(2007181183/5000000000 : ℝ)*X 0 2+(2180721789/5000000000 : ℝ)*X 1 0+(4739271481/10000000000 : ℝ)*X 1 1+(2007181183/5000000000 : ℝ)*X 1 2+(2180721789/5000000000 : ℝ)*X 2 0+(4739271481/10000000000 : ℝ)*X 2 1+(2007181183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1081_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7452631078083483209883516369/1927375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (623440731/100000000000000 : ℝ)*(base19) + (86854009/12500000000000 : ℝ)*(base23) + (33379709/50000000000000 : ℝ)*(upper3) + (384059/10000000000000 : ℝ)*(upper4) + (13887233/20000000000000 : ℝ)*(upper5) + (2015981455478233/100000000000000 : ℝ)*(major0) + (2015981455478233/100000000000000 : ℝ)*(major1) + (2015981455478233/100000000000000 : ℝ)*(major2) + (1336210263467699/50000000000000 : ℝ)*(sp0) + (66810746855381/2500000000000 : ℝ)*(sp1) + (1336214901411949/50000000000000 : ℝ)*(sp2) + (679764069653981/50000000000000 : ℝ)*(sp3) + (9970720573/100000000000000 : ℝ)*(sp4) + (518137707/12500000000000 : ℝ)*(sp7) + (1359532284409617/100000000000000 : ℝ)*(f.failure) + (267243049765597/10000000000000 : ℝ)*(f.sum) + (172724399084221/38547500000000000000000000000 : ℝ)*base66 + (70399114437181177877/7709500000000000000000000000000000 : ℝ)*base68 + (127033320895808177877/7709500000000000000000000000000000 : ℝ)*base70 + (81085284088645177877/7709500000000000000000000000000000 : ℝ)*base72 + (63278699740611/38547500000000000000000000000 : ℝ)*base74 + (74590439543486177877/7709500000000000000000000000000000 : ℝ)*base76 + (118024274024064177877/7709500000000000000000000000000000 : ℝ)*base78 + (57231757792910822123/7709500000000000000000000000000000 : ℝ)*base79 + (65896145472929/9636875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5057041/10000000000000000000000 : ℝ)*base90 + (5057041/10000000000000000000000 : ℝ)*base92 + (5057041/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11168799053698176649897409031/1927375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1128838169/100000000000000 : ℝ)*(base19) + (1349059143/100000000000000 : ℝ)*(base23) + (164582051/100000000000000 : ℝ)*(upper3) + (30423009/100000000000000 : ℝ)*(lower4) + (113451953/100000000000000 : ℝ)*(upper5) + (1022783295763189/50000000000000 : ℝ)*(major0) + (1022783295763189/50000000000000 : ℝ)*(major1) + (1022783295763189/50000000000000 : ℝ)*(major2) + (4938269983/50000000000000 : ℝ)*(sp1) + (12164380017/100000000000000 : ℝ)*(sp2) + (2711649159059717/100000000000000 : ℝ)*(sp4) + (1355819076840791/50000000000000 : ℝ)*(sp5) + (2711635645620557/100000000000000 : ℝ)*(sp6) + (172435478854029/12500000000000 : ℝ)*(sp7) + (172435478854029/12500000000000 : ℝ)*(f.failure) + (2711649159059717/100000000000000 : ℝ)*(f.sum) + (183561390187081/38547500000000000000000000000 : ℝ)*base66 + (4203781640808993441/3854750000000000000000000000000000 : ℝ)*base68 + (19911717055998493441/3854750000000000000000000000000000 : ℝ)*base70 + (32623226447314493441/3854750000000000000000000000000000 : ℝ)*base72 + (45854388033989/38547500000000000000000000000 : ℝ)*base73 + (33621816758060993441/3854750000000000000000000000000000 : ℝ)*base76 + (13806639740271743441/3854750000000000000000000000000000 : ℝ)*base78 + (12056281255301993441/3854750000000000000000000000000000 : ℝ)*base80 + (107169117029427/77095000000000000000000000000 : ℝ)*base82 + (8920883/1250000000000000000000 : ℝ)*base89 + (8920883/1250000000000000000000 : ℝ)*base91 + (8920883/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1081_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (259/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1757/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4173/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1081_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1081_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1757/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4173/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1081_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1081_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1081_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8273/2048 : ℝ) ≤ p) (hpb : p ≤ (4137/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148284927/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1757/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4173/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1081_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
