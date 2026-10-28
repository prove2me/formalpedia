-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:28.103717+00:00
-- url     : https://prove2.me/submissions/a54ca10a-e52a-4728-8427-d0ee6002af9d

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
theorem support_rectangle_w1074_s0_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-47838017/250000000 : ℝ)*x 0 + (189693141/312500000 : ℝ)*x 1 + (477181241/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47838017/250000000 : ℝ)^8267 ≤ (2220042026791/20000000000000 : ℝ)^6219 := by
    have hnat : (47838017 : ℕ)^8267*20000000000000^6219 ≤ 2220042026791^6219*250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47838017 250000000 2220042026791 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189693141/312500000 : ℝ)^8267 ≤ (10299994356753/20000000000000 : ℝ)^6219 := by
    have hnat : (189693141 : ℕ)^8267*20000000000000^6219 ≤ 10299994356753^6219*312500000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189693141 312500000 10299994356753 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477181241/1000000000 : ℝ)^8267 ≤ (37399818074929/100000000000000 : ℝ)^6219 := by
    have hnat : (477181241 : ℕ)^8267*100000000000000^6219 ≤ 37399818074929^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477181241 1000000000 37399818074929 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47838017/250000000 : ℝ), (189693141/312500000 : ℝ), (477181241/1000000000 : ℝ)] ![(2220042026791/20000000000000 : ℝ), (10299994356753/20000000000000 : ℝ), (37399818074929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47838017/250000000 : ℝ)|^8267 ≤ (2220042026791/20000000000000 : ℝ)^6219
        have hw : |(-47838017/250000000 : ℝ)|=(47838017/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(189693141/312500000 : ℝ)|^8267 ≤ (10299994356753/20000000000000 : ℝ)^6219
        have hw : |(189693141/312500000 : ℝ)|=(189693141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477181241/1000000000 : ℝ)|^8267 ≤ (37399818074929/100000000000000 : ℝ)^6219
        have hw : |(477181241/1000000000 : ℝ)|=(477181241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86259731/156250000 : ℝ)*x 0 + (-2660630119/10000000000 : ℝ)*x 1 + (4771812629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86259731/156250000 : ℝ)^8267 ≤ (45396387046091/100000000000000 : ℝ)^6219 := by
    have hnat : (86259731 : ℕ)^8267*100000000000000^6219 ≤ 45396387046091^6219*156250000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86259731 156250000 45396387046091 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2660630119/10000000000 : ℝ)^8267 ≤ (8601896293513/50000000000000 : ℝ)^6219 := by
    have hnat : (2660630119 : ℕ)^8267*50000000000000^6219 ≤ 8601896293513^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660630119 10000000000 8601896293513 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771812629/10000000000 : ℝ)^8267 ≤ (2337488772289/6250000000000 : ℝ)^6219 := by
    have hnat : (4771812629 : ℕ)^8267*6250000000000^6219 ≤ 2337488772289^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771812629 10000000000 2337488772289 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86259731/156250000 : ℝ), (-2660630119/10000000000 : ℝ), (4771812629/10000000000 : ℝ)] ![(45396387046091/100000000000000 : ℝ), (8601896293513/50000000000000 : ℝ), (2337488772289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86259731/156250000 : ℝ)|^8267 ≤ (45396387046091/100000000000000 : ℝ)^6219
        have hw : |(86259731/156250000 : ℝ)|=(86259731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2660630119/10000000000 : ℝ)|^8267 ≤ (8601896293513/50000000000000 : ℝ)^6219
        have hw : |(-2660630119/10000000000 : ℝ)|=(2660630119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771812629/10000000000 : ℝ)|^8267 ≤ (2337488772289/6250000000000 : ℝ)^6219
        have hw : |(4771812629/10000000000 : ℝ)|=(4771812629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520622729/10000000000 : ℝ)*x 0 + (4771812561/10000000000 : ℝ)*x 1 + (-266063027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520622729/10000000000 : ℝ)^8267 ≤ (9079277288977/20000000000000 : ℝ)^6219 := by
    have hnat : (5520622729 : ℕ)^8267*20000000000000^6219 ≤ 9079277288977^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520622729 10000000000 9079277288977 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4771812561/10000000000 : ℝ)^8267 ≤ (4674977456019/12500000000000 : ℝ)^6219 := by
    have hnat : (4771812561 : ℕ)^8267*12500000000000^6219 ≤ 4674977456019^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771812561 10000000000 4674977456019 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266063027/1000000000 : ℝ)^8267 ≤ (8601896942467/50000000000000 : ℝ)^6219 := by
    have hnat : (266063027 : ℕ)^8267*50000000000000^6219 ≤ 8601896942467^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266063027 1000000000 8601896942467 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520622729/10000000000 : ℝ), (4771812561/10000000000 : ℝ), (-266063027/1000000000 : ℝ)] ![(9079277288977/20000000000000 : ℝ), (4674977456019/12500000000000 : ℝ), (8601896942467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520622729/10000000000 : ℝ)|^8267 ≤ (9079277288977/20000000000000 : ℝ)^6219
        have hw : |(5520622729/10000000000 : ℝ)|=(5520622729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4771812561/10000000000 : ℝ)|^8267 ≤ (4674977456019/12500000000000 : ℝ)^6219
        have hw : |(4771812561/10000000000 : ℝ)|=(4771812561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266063027/1000000000 : ℝ)|^8267 ≤ (8601896942467/50000000000000 : ℝ)^6219
        have hw : |(-266063027/1000000000 : ℝ)|=(266063027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206547523/10000000000 : ℝ)*x 0 + (31244423/100000000 : ℝ)*x 1 + (354569079/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206547523/10000000000 : ℝ)^8267 ≤ (6325713581829/20000000000000 : ℝ)^6219 := by
    have hnat : (4206547523 : ℕ)^8267*20000000000000^6219 ≤ 6325713581829^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206547523 10000000000 6325713581829 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31244423/100000000 : ℝ)^8267 ≤ (21300722216251/100000000000000 : ℝ)^6219 := by
    have hnat : (31244423 : ℕ)^8267*100000000000000^6219 ≤ 21300722216251^6219*100000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31244423 100000000 21300722216251 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354569079/625000000 : ℝ)^8267 ≤ (11767677463079/25000000000000 : ℝ)^6219 := by
    have hnat : (354569079 : ℕ)^8267*25000000000000^6219 ≤ 11767677463079^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354569079 625000000 11767677463079 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206547523/10000000000 : ℝ), (31244423/100000000 : ℝ), (354569079/625000000 : ℝ)] ![(6325713581829/20000000000000 : ℝ), (21300722216251/100000000000000 : ℝ), (11767677463079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206547523/10000000000 : ℝ)|^8267 ≤ (6325713581829/20000000000000 : ℝ)^6219
        have hw : |(4206547523/10000000000 : ℝ)|=(4206547523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31244423/100000000 : ℝ)|^8267 ≤ (21300722216251/100000000000000 : ℝ)^6219
        have hw : |(31244423/100000000 : ℝ)|=(31244423/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(354569079/625000000 : ℝ)|^8267 ≤ (11767677463079/25000000000000 : ℝ)^6219
        have hw : |(354569079/625000000 : ℝ)|=(354569079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-959434813/5000000000 : ℝ)*x 0 + (4805334239/10000000000 : ℝ)*x 1 + (1508871351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959434813/5000000000 : ℝ)^8267 ≤ (696342264213/6250000000000 : ℝ)^6219 := by
    have hnat : (959434813 : ℕ)^8267*6250000000000^6219 ≤ 696342264213^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959434813 5000000000 696342264213 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805334239/10000000000 : ℝ)^8267 ≤ (37749475286911/100000000000000 : ℝ)^6219 := by
    have hnat : (4805334239 : ℕ)^8267*100000000000000^6219 ≤ 37749475286911^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805334239 10000000000 37749475286911 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508871351/2500000000 : ℝ)^8267 ≤ (51109048472397/100000000000000 : ℝ)^6219 := by
    have hnat : (1508871351 : ℕ)^8267*100000000000000^6219 ≤ 51109048472397^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508871351 2500000000 51109048472397 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959434813/5000000000 : ℝ), (4805334239/10000000000 : ℝ), (1508871351/2500000000 : ℝ)] ![(696342264213/6250000000000 : ℝ), (37749475286911/100000000000000 : ℝ), (51109048472397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959434813/5000000000 : ℝ)|^8267 ≤ (696342264213/6250000000000 : ℝ)^6219
        have hw : |(-959434813/5000000000 : ℝ)|=(959434813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805334239/10000000000 : ℝ)|^8267 ≤ (37749475286911/100000000000000 : ℝ)^6219
        have hw : |(4805334239/10000000000 : ℝ)|=(4805334239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1508871351/2500000000 : ℝ)|^8267 ≤ (51109048472397/100000000000000 : ℝ)^6219
        have hw : |(1508871351/2500000000 : ℝ)|=(1508871351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646022691/1250000000 : ℝ)*x 0 + (-698480443/5000000000 : ℝ)*x 1 + (6035483287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646022691/1250000000 : ℝ)^8267 ≤ (81220579353/195312500000 : ℝ)^6219 := by
    have hnat : (646022691 : ℕ)^8267*195312500000^6219 ≤ 81220579353^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646022691 1250000000 81220579353 195312500000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698480443/5000000000 : ℝ)^8267 ≤ (913254838601/12500000000000 : ℝ)^6219 := by
    have hnat : (698480443 : ℕ)^8267*12500000000000^6219 ≤ 913254838601^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698480443 5000000000 913254838601 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6035483287/10000000000 : ℝ)^8267 ≤ (51109024641861/100000000000000 : ℝ)^6219 := by
    have hnat : (6035483287 : ℕ)^8267*100000000000000^6219 ≤ 51109024641861^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035483287 10000000000 51109024641861 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646022691/1250000000 : ℝ), (-698480443/5000000000 : ℝ), (6035483287/10000000000 : ℝ)] ![(81220579353/195312500000 : ℝ), (913254838601/12500000000000 : ℝ), (51109024641861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646022691/1250000000 : ℝ)|^8267 ≤ (81220579353/195312500000 : ℝ)^6219
        have hw : |(646022691/1250000000 : ℝ)|=(646022691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698480443/5000000000 : ℝ)|^8267 ≤ (913254838601/12500000000000 : ℝ)^6219
        have hw : |(-698480443/5000000000 : ℝ)|=(698480443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6035483287/10000000000 : ℝ)|^8267 ≤ (51109024641861/100000000000000 : ℝ)^6219
        have hw : |(6035483287/10000000000 : ℝ)|=(6035483287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646022679/1250000000 : ℝ)*x 0 + (6035484813/10000000000 : ℝ)*x 1 + (-349239641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646022679/1250000000 : ℝ)^8267 ≤ (4158493560191/10000000000000 : ℝ)^6219 := by
    have hnat : (646022679 : ℕ)^8267*10000000000000^6219 ≤ 4158493560191^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646022679 1250000000 4158493560191 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6035484813/10000000000 : ℝ)^8267 ≤ (51109041819659/100000000000000 : ℝ)^6219 := by
    have hnat : (6035484813 : ℕ)^8267*100000000000000^6219 ≤ 51109041819659^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035484813 10000000000 51109041819659 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349239641/2500000000 : ℝ)^8267 ≤ (3653011282849/50000000000000 : ℝ)^6219 := by
    have hnat : (349239641 : ℕ)^8267*50000000000000^6219 ≤ 3653011282849^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349239641 2500000000 3653011282849 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646022679/1250000000 : ℝ), (6035484813/10000000000 : ℝ), (-349239641/2500000000 : ℝ)] ![(4158493560191/10000000000000 : ℝ), (51109041819659/100000000000000 : ℝ), (3653011282849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646022679/1250000000 : ℝ)|^8267 ≤ (4158493560191/10000000000000 : ℝ)^6219
        have hw : |(646022679/1250000000 : ℝ)|=(646022679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6035484813/10000000000 : ℝ)|^8267 ≤ (51109041819659/100000000000000 : ℝ)^6219
        have hw : |(6035484813/10000000000 : ℝ)|=(6035484813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349239641/2500000000 : ℝ)|^8267 ≤ (3653011282849/50000000000000 : ℝ)^6219
        have hw : |(-349239641/2500000000 : ℝ)|=(349239641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s0_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4217046609/10000000000 : ℝ)*x 0 + (1401824937/2500000000 : ℝ)*x 1 + (1596275059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217046609/10000000000 : ℝ)^8267 ≤ (991673405231/3125000000000 : ℝ)^6219 := by
    have hnat : (4217046609 : ℕ)^8267*3125000000000^6219 ≤ 991673405231^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217046609 10000000000 991673405231 3125000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401824937/2500000000 : ℝ)^8267 ≤ (46346295329729/100000000000000 : ℝ)^6219 := by
    have hnat : (1401824937 : ℕ)^8267*100000000000000^6219 ≤ 46346295329729^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401824937 2500000000 46346295329729 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596275059/5000000000 : ℝ)^8267 ≤ (85625608147/390625000000 : ℝ)^6219 := by
    have hnat : (1596275059 : ℕ)^8267*390625000000^6219 ≤ 85625608147^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596275059 5000000000 85625608147 390625000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217046609/10000000000 : ℝ), (1401824937/2500000000 : ℝ), (1596275059/5000000000 : ℝ)] ![(991673405231/3125000000000 : ℝ), (46346295329729/100000000000000 : ℝ), (85625608147/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217046609/10000000000 : ℝ)|^8267 ≤ (991673405231/3125000000000 : ℝ)^6219
        have hw : |(4217046609/10000000000 : ℝ)|=(4217046609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401824937/2500000000 : ℝ)|^8267 ≤ (46346295329729/100000000000000 : ℝ)^6219
        have hw : |(1401824937/2500000000 : ℝ)|=(1401824937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596275059/5000000000 : ℝ)|^8267 ≤ (85625608147/390625000000 : ℝ)^6219
        have hw : |(1596275059/5000000000 : ℝ)|=(1596275059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (13/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14039/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4133/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4133 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4133*1^1024 ≤ 0^1024*1^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4133/1024 : ℝ) ≤ (619157705668324581/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4133 ≤ (619157705668324581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4133*25000000000000000000^1024 ≤ 619157705668324581^1024*5^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 619157705668324581 25000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (619157705668324581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4133 := by
      have hnat : (1 : ℕ)^1024*1^4133 ≤ 1^4133*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25619157705668324581/25000000000000000000 : ℝ) ≤ (5030399011356139/5000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (25619157705668324581/25000000000000000000 : ℝ)^1024 ≤ (5030399011356139/5000000000000000 : ℝ)^4133 := by
      have hnat : (25619157705668324581 : ℕ)^1024*5000000000000000^4133 ≤ 5030399011356139^4133*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25619157705668324581 25000000000000000000 5030399011356139 5000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030399011356139/5000000000000000 : ℝ)) (X := (25619157705668324581/25000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13119157705668324581/12500000000000000000 : ℝ) ≤ (2530399011356139/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (13119157705668324581/12500000000000000000 : ℝ)^1024 ≤ (2530399011356139/2500000000000000 : ℝ)^4133 := by
      have hnat : (13119157705668324581 : ℕ)^1024*2500000000000000^4133 ≤ 2530399011356139^4133*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13119157705668324581 12500000000000000000 2530399011356139 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530399011356139/2500000000000000 : ℝ)) (X := (13119157705668324581/12500000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30399011356139/2000000000000000 : ℝ)*(0 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30399011356139/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(619157705668324581/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30399011356139/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30399011356139/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030399011356139/5000000000000000 : ℝ) by norm_num, show 1+(619157705668324581/25000000000000000000 : ℝ)+(0 : ℝ)=(25619157705668324581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(619157705668324581/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30399011356139/2000000000000000 : ℝ)*(2/5 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30399011356139/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530399011356139/2500000000000000 : ℝ) by norm_num, show 1+2*(619157705668324581/25000000000000000000 : ℝ)=(13119157705668324581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30399011356139/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30399011356139/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30399011356139/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30399011356139/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30399011356139/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30399011356139/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-47838017/250000000 : ℝ)*X 0 0+(189693141/312500000 : ℝ)*X 0 1+(477181241/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((86259731/156250000 : ℝ)*X 1 0+(-2660630119/10000000000 : ℝ)*X 1 1+(4771812629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520622729/10000000000 : ℝ)*X 2 0+(4771812561/10000000000 : ℝ)*X 2 1+(-266063027/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206547523/10000000000 : ℝ)*X 0 0+(31244423/100000000 : ℝ)*X 0 1+(354569079/625000000 : ℝ)*X 0 2+(4206547523/10000000000 : ℝ)*X 1 0+(31244423/100000000 : ℝ)*X 1 1+(354569079/625000000 : ℝ)*X 1 2+(4206547523/10000000000 : ℝ)*X 2 0+(31244423/100000000 : ℝ)*X 2 1+(354569079/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-959434813/5000000000 : ℝ)*X 0 0+(4805334239/10000000000 : ℝ)*X 0 1+(1508871351/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646022691/1250000000 : ℝ)*X 1 0+(-698480443/5000000000 : ℝ)*X 1 1+(6035483287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646022679/1250000000 : ℝ)*X 2 0+(6035484813/10000000000 : ℝ)*X 2 1+(-349239641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217046609/10000000000 : ℝ)*X 0 0+(1401824937/2500000000 : ℝ)*X 0 1+(1596275059/5000000000 : ℝ)*X 0 2+(4217046609/10000000000 : ℝ)*X 1 0+(1401824937/2500000000 : ℝ)*X 1 1+(1596275059/5000000000 : ℝ)*X 1 2+(4217046609/10000000000 : ℝ)*X 2 0+(1401824937/2500000000 : ℝ)*X 2 1+(1596275059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619838947464519407811807/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2986281/25000000000000 : ℝ)*(base1) + (1531788031/100000000000000 : ℝ)*(base19) + (714933951/50000000000000 : ℝ)*(base23) + (1884937/2000000000000 : ℝ)*(base24) + (176178751/50000000000000 : ℝ)*(upper3) + (581287064537557/100000000000000 : ℝ)*(major0) + (581287064537557/100000000000000 : ℝ)*(major1) + (581287064537557/100000000000000 : ℝ)*(major2) + (770202966104361/100000000000000 : ℝ)*(sp0) + (770205059843239/100000000000000 : ℝ)*(sp1) + (385102533758259/50000000000000 : ℝ)*(sp2) + (98091099461881/25000000000000 : ℝ)*(sp3) + (113671001/3125000000000 : ℝ)*(sp4) + (2921038211/100000000000000 : ℝ)*(sp7) + (392367330830859/100000000000000 : ℝ)*(f.failure) + (770206591631269/100000000000000 : ℝ)*(f.sum) + (63953935887577/100000000000000000000000000000 : ℝ)*base66 + (529142966412423/200000000000000000000000000000 : ℝ)*base67 + (31659766387577/200000000000000000000000000000 : ℝ)*base70 + (53489917387577/200000000000000000000000000000 : ℝ)*base72 + (71771409312423/100000000000000000000000000000 : ℝ)*base73 + (601924644987577/200000000000000000000000000000 : ℝ)*base76 + (85885966587577/200000000000000000000000000000 : ℝ)*base78 + (709350257187577/200000000000000000000000000000 : ℝ)*base80 + (337819069387577/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3255569/10000000000000000000000 : ℝ)*base89 + (3255569/10000000000000000000000 : ℝ)*base91 + (3255569/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (604809770550636742838481/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (307905401/25000000000000 : ℝ)*(base19) + (1401796541/100000000000000 : ℝ)*(base23) + (4191291/3125000000000 : ℝ)*(base39) + (13243687/6250000000000 : ℝ)*(base45) + (104287073/100000000000000 : ℝ)*(upper3) + (314120017/100000000000000 : ℝ)*(upper5) + (613513704248963/100000000000000 : ℝ)*(major0) + (613513704248963/100000000000000 : ℝ)*(major1) + (153378392531913/25000000000000 : ℝ)*(major2) + (807954097/100000000000000 : ℝ)*(sp2) + (812906839845367/100000000000000 : ℝ)*(sp4) + (812905608223763/100000000000000 : ℝ)*(sp5) + (812904764216041/100000000000000 : ℝ)*(sp6) + (414120232927987/100000000000000 : ℝ)*(sp7) + (414120232927987/100000000000000 : ℝ)*(f.failure) + (812906973966679/100000000000000 : ℝ)*(f.sum) + (57057537982103/40000000000000000000000000000 : ℝ)*base66 + (147417433486093/50000000000000000000000000000 : ℝ)*base68 + (624517967633857/200000000000000000000000000000 : ℝ)*base69 + (258863831386093/50000000000000000000000000000 : ℝ)*base72 + (37621134662103/40000000000000000000000000000 : ℝ)*base74 + (14927174966143/200000000000000000000000000000 : ℝ)*base76 + (1017740387166143/200000000000000000000000000000 : ℝ)*base78 + (1047855890766143/200000000000000000000000000000 : ℝ)*base80 + (461158000766143/100000000000000000000000000000 : ℝ)*base82 + (71315017/10000000000000000000000 : ℝ)*base89 + (71315017/10000000000000000000000 : ℝ)*base91 + (28684983/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s1_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061539887/5000000000 : ℝ)*x 0 + (5720085243/10000000000 : ℝ)*x 1 + (997542079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061539887/5000000000 : ℝ)^8267 ≤ (1274463214991/10000000000000 : ℝ)^6219 := by
    have hnat : (1061539887 : ℕ)^8267*10000000000000^6219 ≤ 1274463214991^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061539887 5000000000 1274463214991 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720085243/10000000000 : ℝ)^8267 ≤ (47589582518693/100000000000000 : ℝ)^6219 := by
    have hnat : (5720085243 : ℕ)^8267*100000000000000^6219 ≤ 47589582518693^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720085243 10000000000 47589582518693 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997542079/2000000000 : ℝ)^8267 ≤ (39665785313671/100000000000000 : ℝ)^6219 := by
    have hnat : (997542079 : ℕ)^8267*100000000000000^6219 ≤ 39665785313671^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997542079 2000000000 39665785313671 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061539887/5000000000 : ℝ), (5720085243/10000000000 : ℝ), (997542079/2000000000 : ℝ)] ![(1274463214991/10000000000000 : ℝ), (47589582518693/100000000000000 : ℝ), (39665785313671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061539887/5000000000 : ℝ)|^8267 ≤ (1274463214991/10000000000000 : ℝ)^6219
        have hw : |(-1061539887/5000000000 : ℝ)|=(1061539887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720085243/10000000000 : ℝ)|^8267 ≤ (47589582518693/100000000000000 : ℝ)^6219
        have hw : |(5720085243/10000000000 : ℝ)|=(5720085243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(997542079/2000000000 : ℝ)|^8267 ≤ (39665785313671/100000000000000 : ℝ)^6219
        have hw : |(997542079/2000000000 : ℝ)|=(997542079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5422870473/10000000000 : ℝ)*x 0 + (-2519711473/10000000000 : ℝ)*x 1 + (623463837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422870473/10000000000 : ℝ)^8267 ≤ (44330982572693/100000000000000 : ℝ)^6219 := by
    have hnat : (5422870473 : ℕ)^8267*100000000000000^6219 ≤ 44330982572693^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422870473 10000000000 44330982572693 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519711473/10000000000 : ℝ)^8267 ≤ (16003228922311/100000000000000 : ℝ)^6219 := by
    have hnat : (2519711473 : ℕ)^8267*100000000000000^6219 ≤ 16003228922311^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519711473 10000000000 16003228922311 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623463837/1250000000 : ℝ)^8267 ≤ (39665788495733/100000000000000 : ℝ)^6219 := by
    have hnat : (623463837 : ℕ)^8267*100000000000000^6219 ≤ 39665788495733^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623463837 1250000000 39665788495733 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422870473/10000000000 : ℝ), (-2519711473/10000000000 : ℝ), (623463837/1250000000 : ℝ)] ![(44330982572693/100000000000000 : ℝ), (16003228922311/100000000000000 : ℝ), (39665788495733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422870473/10000000000 : ℝ)|^8267 ≤ (44330982572693/100000000000000 : ℝ)^6219
        have hw : |(5422870473/10000000000 : ℝ)|=(5422870473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2519711473/10000000000 : ℝ)|^8267 ≤ (16003228922311/100000000000000 : ℝ)^6219
        have hw : |(-2519711473/10000000000 : ℝ)|=(2519711473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623463837/1250000000 : ℝ)|^8267 ≤ (39665788495733/100000000000000 : ℝ)^6219
        have hw : |(623463837/1250000000 : ℝ)|=(623463837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711435569/5000000000 : ℝ)*x 0 + (2493854983/5000000000 : ℝ)*x 1 + (-2519711531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711435569/5000000000 : ℝ)^8267 ≤ (44330989799179/100000000000000 : ℝ)^6219 := by
    have hnat : (2711435569 : ℕ)^8267*100000000000000^6219 ≤ 44330989799179^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711435569 5000000000 44330989799179 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493854983/5000000000 : ℝ)^8267 ≤ (39665780778439/100000000000000 : ℝ)^6219 := by
    have hnat : (2493854983 : ℕ)^8267*100000000000000^6219 ≤ 39665780778439^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493854983 5000000000 39665780778439 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2519711531/10000000000 : ℝ)^8267 ≤ (16003229411991/100000000000000 : ℝ)^6219 := by
    have hnat : (2519711531 : ℕ)^8267*100000000000000^6219 ≤ 16003229411991^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519711531 10000000000 16003229411991 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711435569/5000000000 : ℝ), (2493854983/5000000000 : ℝ), (-2519711531/10000000000 : ℝ)] ![(44330989799179/100000000000000 : ℝ), (39665780778439/100000000000000 : ℝ), (16003229411991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711435569/5000000000 : ℝ)|^8267 ≤ (44330989799179/100000000000000 : ℝ)^6219
        have hw : |(2711435569/5000000000 : ℝ)|=(2711435569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2493854983/5000000000 : ℝ)|^8267 ≤ (39665780778439/100000000000000 : ℝ)^6219
        have hw : |(2493854983/5000000000 : ℝ)|=(2493854983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2519711531/10000000000 : ℝ)|^8267 ≤ (16003229411991/100000000000000 : ℝ)^6219
        have hw : |(-2519711531/10000000000 : ℝ)|=(2519711531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172925553/400000000 : ℝ)*x 0 + (229005253/625000000 : ℝ)*x 1 + (5101715281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172925553/400000000 : ℝ)^8267 ≤ (1311967163647/4000000000000 : ℝ)^6219 := by
    have hnat : (172925553 : ℕ)^8267*4000000000000^6219 ≤ 1311967163647^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172925553 400000000 1311967163647 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229005253/625000000 : ℝ)^8267 ≤ (3290663051287/12500000000000 : ℝ)^6219 := by
    have hnat : (229005253 : ℕ)^8267*12500000000000^6219 ≤ 3290663051287^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229005253 625000000 3290663051287 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5101715281/10000000000 : ℝ)^8267 ≤ (20437758236219/50000000000000 : ℝ)^6219 := by
    have hnat : (5101715281 : ℕ)^8267*50000000000000^6219 ≤ 20437758236219^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101715281 10000000000 20437758236219 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172925553/400000000 : ℝ), (229005253/625000000 : ℝ), (5101715281/10000000000 : ℝ)] ![(1311967163647/4000000000000 : ℝ), (3290663051287/12500000000000 : ℝ), (20437758236219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172925553/400000000 : ℝ)|^8267 ≤ (1311967163647/4000000000000 : ℝ)^6219
        have hw : |(172925553/400000000 : ℝ)|=(172925553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229005253/625000000 : ℝ)|^8267 ≤ (3290663051287/12500000000000 : ℝ)^6219
        have hw : |(229005253/625000000 : ℝ)|=(229005253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5101715281/10000000000 : ℝ)|^8267 ≤ (20437758236219/50000000000000 : ℝ)^6219
        have hw : |(5101715281/10000000000 : ℝ)|=(5101715281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212398951/1000000000 : ℝ)*x 0 + (4997971907/10000000000 : ℝ)*x 1 + (11419227/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212398951/1000000000 : ℝ)^8267 ≤ (12751892112643/100000000000000 : ℝ)^6219 := by
    have hnat : (212398951 : ℕ)^8267*100000000000000^6219 ≤ 12751892112643^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212398951 1000000000 12751892112643 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997971907/10000000000 : ℝ)^8267 ≤ (39774303017203/100000000000000 : ℝ)^6219 := by
    have hnat : (4997971907 : ℕ)^8267*100000000000000^6219 ≤ 39774303017203^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997971907 10000000000 39774303017203 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11419227/20000000 : ℝ)^8267 ≤ (1898952194383/4000000000000 : ℝ)^6219 := by
    have hnat : (11419227 : ℕ)^8267*4000000000000^6219 ≤ 1898952194383^6219*20000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11419227 20000000 1898952194383 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212398951/1000000000 : ℝ), (4997971907/10000000000 : ℝ), (11419227/20000000 : ℝ)] ![(12751892112643/100000000000000 : ℝ), (39774303017203/100000000000000 : ℝ), (1898952194383/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212398951/1000000000 : ℝ)|^8267 ≤ (12751892112643/100000000000000 : ℝ)^6219
        have hw : |(-212398951/1000000000 : ℝ)|=(212398951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997971907/10000000000 : ℝ)|^8267 ≤ (39774303017203/100000000000000 : ℝ)^6219
        have hw : |(4997971907/10000000000 : ℝ)|=(4997971907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11419227/20000000 : ℝ)|^8267 ≤ (1898952194383/4000000000000 : ℝ)^6219
        have hw : |(11419227/20000000 : ℝ)|=(11419227/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52357549/100000000 : ℝ)*x 0 + (-179780621/1000000000 : ℝ)*x 1 + (71370193/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52357549/100000000 : ℝ)^8267 ≤ (42309260031909/100000000000000 : ℝ)^6219 := by
    have hnat : (52357549 : ℕ)^8267*100000000000000^6219 ≤ 42309260031909^6219*100000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52357549 100000000 42309260031909 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179780621/1000000000 : ℝ)^8267 ≤ (10216913654763/100000000000000 : ℝ)^6219 := by
    have hnat : (179780621 : ℕ)^8267*100000000000000^6219 ≤ 10216913654763^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179780621 1000000000 10216913654763 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71370193/125000000 : ℝ)^8267 ≤ (47473826302127/100000000000000 : ℝ)^6219 := by
    have hnat : (71370193 : ℕ)^8267*100000000000000^6219 ≤ 47473826302127^6219*125000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71370193 125000000 47473826302127 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52357549/100000000 : ℝ), (-179780621/1000000000 : ℝ), (71370193/125000000 : ℝ)] ![(42309260031909/100000000000000 : ℝ), (10216913654763/100000000000000 : ℝ), (47473826302127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52357549/100000000 : ℝ)|^8267 ≤ (42309260031909/100000000000000 : ℝ)^6219
        have hw : |(52357549/100000000 : ℝ)|=(52357549/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179780621/1000000000 : ℝ)|^8267 ≤ (10216913654763/100000000000000 : ℝ)^6219
        have hw : |(-179780621/1000000000 : ℝ)|=(179780621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71370193/125000000 : ℝ)|^8267 ≤ (47473826302127/100000000000000 : ℝ)^6219
        have hw : |(71370193/125000000 : ℝ)|=(71370193/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5235752833/10000000000 : ℝ)*x 0 + (5709617733/10000000000 : ℝ)*x 1 + (-898902897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235752833/10000000000 : ℝ)^8267 ≤ (1057730945707/2500000000000 : ℝ)^6219 := by
    have hnat : (5235752833 : ℕ)^8267*2500000000000^6219 ≤ 1057730945707^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235752833 10000000000 1057730945707 2500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5709617733/10000000000 : ℝ)^8267 ≤ (23736925823171/50000000000000 : ℝ)^6219 := by
    have hnat : (5709617733 : ℕ)^8267*50000000000000^6219 ≤ 23736925823171^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5709617733 10000000000 23736925823171 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898902897/5000000000 : ℝ)^8267 ≤ (5108455256051/50000000000000 : ℝ)^6219 := by
    have hnat : (898902897 : ℕ)^8267*50000000000000^6219 ≤ 5108455256051^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898902897 5000000000 5108455256051 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235752833/10000000000 : ℝ), (5709617733/10000000000 : ℝ), (-898902897/5000000000 : ℝ)] ![(1057730945707/2500000000000 : ℝ), (23736925823171/50000000000000 : ℝ), (5108455256051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235752833/10000000000 : ℝ)|^8267 ≤ (1057730945707/2500000000000 : ℝ)^6219
        have hw : |(5235752833/10000000000 : ℝ)|=(5235752833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5709617733/10000000000 : ℝ)|^8267 ≤ (23736925823171/50000000000000 : ℝ)^6219
        have hw : |(5709617733/10000000000 : ℝ)|=(5709617733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898902897/5000000000 : ℝ)|^8267 ≤ (5108455256051/50000000000000 : ℝ)^6219
        have hw : |(-898902897/5000000000 : ℝ)|=(898902897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s1_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081230053/2500000000 : ℝ)*x 0 + (1270392197/2500000000 : ℝ)*x 1 + (1842317947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081230053/2500000000 : ℝ)^8267 ≤ (32817146229617/100000000000000 : ℝ)^6219 := by
    have hnat : (1081230053 : ℕ)^8267*100000000000000^6219 ≤ 32817146229617^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081230053 2500000000 32817146229617 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270392197/2500000000 : ℝ)^8267 ≤ (40661083708549/100000000000000 : ℝ)^6219 := by
    have hnat : (1270392197 : ℕ)^8267*100000000000000^6219 ≤ 40661083708549^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270392197 2500000000 40661083708549 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842317947/5000000000 : ℝ)^8267 ≤ (26521770048263/100000000000000 : ℝ)^6219 := by
    have hnat : (1842317947 : ℕ)^8267*100000000000000^6219 ≤ 26521770048263^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842317947 5000000000 26521770048263 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081230053/2500000000 : ℝ), (1270392197/2500000000 : ℝ), (1842317947/5000000000 : ℝ)] ![(32817146229617/100000000000000 : ℝ), (40661083708549/100000000000000 : ℝ), (26521770048263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081230053/2500000000 : ℝ)|^8267 ≤ (32817146229617/100000000000000 : ℝ)^6219
        have hw : |(1081230053/2500000000 : ℝ)|=(1081230053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270392197/2500000000 : ℝ)|^8267 ≤ (40661083708549/100000000000000 : ℝ)^6219
        have hw : |(1270392197/2500000000 : ℝ)|=(1270392197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842317947/5000000000 : ℝ)|^8267 ≤ (26521770048263/100000000000000 : ℝ)^6219
        have hw : |(1842317947/5000000000 : ℝ)|=(1842317947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (263/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (13/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (13/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (13/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (13/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (13/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (13/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (13/10000 : ℝ) ^ (4133/1024 : ℝ) ≤ (112321287/50000000000000000000 : ℝ) := by
    have hpowers : (13/10000 : ℝ)^4133 ≤ (112321287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (13 : ℕ)^4133*50000000000000000000^1024 ≤ 112321287^1024*10000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 10000 112321287 50000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/10000 : ℝ)) (X := (112321287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14039/50000 : ℝ) ^ (4133/1024 : ℝ) ≤ (593652904602870713/100000000000000000000 : ℝ) := by
    have hpowers : (14039/50000 : ℝ)^4133 ≤ (593652904602870713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14039 : ℕ)^4133*100000000000000000000^1024 ≤ 593652904602870713^1024*50000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14039 50000 593652904602870713 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14039/50000 : ℝ)) (X := (593652904602870713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000112321287/25000000000000000000 : ℝ) ≤ (2500000000002783/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (25000000000112321287/25000000000000000000 : ℝ)^1024 ≤ (2500000000002783/2500000000000000 : ℝ)^4133 := by
      have hnat : (25000000000112321287 : ℕ)^1024*2500000000000000^4133 ≤ 2500000000002783^4133*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000112321287 25000000000000000000 2500000000002783 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000002783/2500000000000000 : ℝ)) (X := (25000000000112321287/25000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100593652904827513287/100000000000000000000 : ℝ) ≤ (2503668932471377/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100593652904827513287/100000000000000000000 : ℝ)^1024 ≤ (2503668932471377/2500000000000000 : ℝ)^4133 := by
      have hnat : (100593652904827513287 : ℕ)^1024*2500000000000000^4133 ≤ 2503668932471377^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100593652904827513287 100000000000000000000 2503668932471377 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503668932471377/2500000000000000 : ℝ)) (X := (100593652904827513287/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50593652904602870713/50000000000000000000 : ℝ) ≤ (2507337864939971/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50593652904602870713/50000000000000000000 : ℝ)^1024 ≤ (2507337864939971/2500000000000000 : ℝ)^4133 := by
      have hnat : (50593652904602870713 : ℕ)^1024*2500000000000000^4133 ≤ 2507337864939971^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50593652904602870713 50000000000000000000 2507337864939971 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507337864939971/2500000000000000 : ℝ)) (X := (50593652904602870713/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112321287/50000000000000000000 : ℝ) ≤ ((17467261519408986211/17467500000000000000 : ℝ)+2*(1834466234297/349350000000000 : ℝ)*(13/10000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (17467261519408986211/17467500000000000000 : ℝ)+2*(1834466234297/349350000000000 : ℝ)*(13/10000 : ℝ)=(2500000000002783/2500000000000000 : ℝ) by norm_num, show 1+2*(112321287/50000000000000000000 : ℝ)=(25000000000112321287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(593652904602870713/100000000000000000000 : ℝ)+(112321287/50000000000000000000 : ℝ) ≤ ((17467261519408986211/17467500000000000000 : ℝ)+(1834466234297/349350000000000 : ℝ)*((14039/50000 : ℝ)+(13/10000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (17467261519408986211/17467500000000000000 : ℝ)+(1834466234297/349350000000000 : ℝ)*((14039/50000 : ℝ)+(13/10000 : ℝ))=(2503668932471377/2500000000000000 : ℝ) by norm_num, show 1+(593652904602870713/100000000000000000000 : ℝ)+(112321287/50000000000000000000 : ℝ)=(100593652904827513287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(593652904602870713/100000000000000000000 : ℝ) ≤ ((17467261519408986211/17467500000000000000 : ℝ)+2*(1834466234297/349350000000000 : ℝ)*(14039/50000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (17467261519408986211/17467500000000000000 : ℝ)+2*(1834466234297/349350000000000 : ℝ)*(14039/50000 : ℝ)=(2507337864939971/2500000000000000 : ℝ) by norm_num, show 1+2*(593652904602870713/100000000000000000000 : ℝ)=(50593652904602870713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17467261519408986211/17467500000000000000 : ℝ)*(X 1 0+X 2 0)+(1834466234297/349350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (13/10000 : ℝ)) (hi := (14039/50000 : ℝ)) (c := (17467261519408986211/17467500000000000000 : ℝ)) (alpha := (1834466234297/349350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17467261519408986211/17467500000000000000 : ℝ)*(X 0 1+X 2 1)+(1834466234297/349350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (13/10000 : ℝ)) (hi := (14039/50000 : ℝ)) (c := (17467261519408986211/17467500000000000000 : ℝ)) (alpha := (1834466234297/349350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17467261519408986211/17467500000000000000 : ℝ)*(X 0 2+X 1 2)+(1834466234297/349350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (13/10000 : ℝ)) (hi := (14039/50000 : ℝ)) (c := (17467261519408986211/17467500000000000000 : ℝ)) (alpha := (1834466234297/349350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061539887/5000000000 : ℝ)*X 0 0+(5720085243/10000000000 : ℝ)*X 0 1+(997542079/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422870473/10000000000 : ℝ)*X 1 0+(-2519711473/10000000000 : ℝ)*X 1 1+(623463837/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711435569/5000000000 : ℝ)*X 2 0+(2493854983/5000000000 : ℝ)*X 2 1+(-2519711531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172925553/400000000 : ℝ)*X 0 0+(229005253/625000000 : ℝ)*X 0 1+(5101715281/10000000000 : ℝ)*X 0 2+(172925553/400000000 : ℝ)*X 1 0+(229005253/625000000 : ℝ)*X 1 1+(5101715281/10000000000 : ℝ)*X 1 2+(172925553/400000000 : ℝ)*X 2 0+(229005253/625000000 : ℝ)*X 2 1+(5101715281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-212398951/1000000000 : ℝ)*X 0 0+(4997971907/10000000000 : ℝ)*X 0 1+(11419227/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52357549/100000000 : ℝ)*X 1 0+(-179780621/1000000000 : ℝ)*X 1 1+(71370193/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5235752833/10000000000 : ℝ)*X 2 0+(5709617733/10000000000 : ℝ)*X 2 1+(-898902897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081230053/2500000000 : ℝ)*X 0 0+(1270392197/2500000000 : ℝ)*X 0 1+(1842317947/5000000000 : ℝ)*X 0 2+(1081230053/2500000000 : ℝ)*X 1 0+(1270392197/2500000000 : ℝ)*X 1 1+(1842317947/5000000000 : ℝ)*X 1 2+(1081230053/2500000000 : ℝ)*X 2 0+(1270392197/2500000000 : ℝ)*X 2 1+(1842317947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10560111011202890093246377/1819531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (124365807/100000000000000 : ℝ)*(base1) + (1965173/160000000000 : ℝ)*(base19) + (1395674379/100000000000000 : ℝ)*(base23) + (295789/250000000000 : ℝ)*(upper3) + (36016683/25000000000000 : ℝ)*(upper5) + (51525696917503/5000000000000 : ℝ)*(major0) + (51525696917503/5000000000000 : ℝ)*(major1) + (51525696917503/5000000000000 : ℝ)*(major2) + (1365426849108261/100000000000000 : ℝ)*(sp0) + (1365432095453877/100000000000000 : ℝ)*(sp1) + (1365431928012623/100000000000000 : ℝ)*(sp2) + (695591383533659/100000000000000 : ℝ)*(sp3) + (1649736137/25000000000000 : ℝ)*(sp4) + (2851655193/100000000000000 : ℝ)*(sp7) + (347797179777329/50000000000000 : ℝ)*(f.failure) + (682716661843501/50000000000000 : ℝ)*(f.sum) + (19799792703611/6987000000000000000000000000 : ℝ)*base66 + (406580394529538633/87337500000000000000000000000000 : ℝ)*base67 + (368969499778798867/87337500000000000000000000000000 : ℝ)*base70 + (175450001469448867/87337500000000000000000000000000 : ℝ)*base72 + (16587875877763/6987000000000000000000000000 : ℝ)*base73 + (229692152455536367/87337500000000000000000000000000 : ℝ)*base76 + (162323275919586367/87337500000000000000000000000000 : ℝ)*base78 + (126230352637123867/87337500000000000000000000000000 : ℝ)*base80 + (5582652137267/1746750000000000000000000000 : ℝ)*base82 + (37173661/5000000000000000000000 : ℝ)*base90 + (37173661/5000000000000000000000 : ℝ)*base92 + (37173661/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624278409707373802985492559/291125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484183357/20000000000000 : ℝ)*(base19) + (120959529/5000000000000 : ℝ)*(base23) + (64882873/25000000000000 : ℝ)*(upper2) + (105058473/25000000000000 : ℝ)*(upper3) + (131176609/25000000000000 : ℝ)*(upper5) + (1060526611156977/100000000000000 : ℝ)*(major0) + (1060526611156977/100000000000000 : ℝ)*(major1) + (1060526611156977/100000000000000 : ℝ)*(major2) + (6171460817/50000000000000 : ℝ)*(sp1) + (1743378333/12500000000000 : ℝ)*(sp2) + (1405200311367903/100000000000000 : ℝ)*(sp4) + (351296386882371/25000000000000 : ℝ)*(sp5) + (702591972575329/50000000000000 : ℝ)*(sp6) + (89481604933399/12500000000000 : ℝ)*(sp7) + (89481604933399/12500000000000 : ℝ)*(f.failure) + (1405200311367903/100000000000000 : ℝ)*(f.sum) + (7834166231527/1455625000000000000000000000 : ℝ)*base65 + (2579295190546048049/582250000000000000000000000000000 : ℝ)*base67 + (974744712946298049/582250000000000000000000000000000 : ℝ)*base69 + (161114945570798049/582250000000000000000000000000000 : ℝ)*base71 + (9107527185027/1455625000000000000000000000 : ℝ)*base73 + (2687875758647298049/582250000000000000000000000000000 : ℝ)*base75 + (4214533757606798049/582250000000000000000000000000000 : ℝ)*base77 + (6982007260572798049/582250000000000000000000000000000 : ℝ)*base79 + (1321897331647/5822500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8469291/1250000000000000000000 : ℝ)*base90 + (8469291/1250000000000000000000 : ℝ)*base92 + (8469291/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (263/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s2_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436009919/2000000000 : ℝ)*x 0 + (44194083/80000000 : ℝ)*x 1 + (5147382281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436009919/2000000000 : ℝ)^8267 ≤ (13201232796773/100000000000000 : ℝ)^6219 := by
    have hnat : (436009919 : ℕ)^8267*100000000000000^6219 ≤ 13201232796773^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436009919 2000000000 13201232796773 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44194083/80000000 : ℝ)^8267 ≤ (11359038482763/25000000000000 : ℝ)^6219 := by
    have hnat : (44194083 : ℕ)^8267*25000000000000^6219 ≤ 11359038482763^6219*80000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44194083 80000000 11359038482763 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147382281/10000000000 : ℝ)^8267 ≤ (41362613249881/100000000000000 : ℝ)^6219 := by
    have hnat : (5147382281 : ℕ)^8267*100000000000000^6219 ≤ 41362613249881^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147382281 10000000000 41362613249881 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436009919/2000000000 : ℝ), (44194083/80000000 : ℝ), (5147382281/10000000000 : ℝ)] ![(13201232796773/100000000000000 : ℝ), (11359038482763/25000000000000 : ℝ), (41362613249881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436009919/2000000000 : ℝ)|^8267 ≤ (13201232796773/100000000000000 : ℝ)^6219
        have hw : |(-436009919/2000000000 : ℝ)|=(436009919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44194083/80000000 : ℝ)|^8267 ≤ (11359038482763/25000000000000 : ℝ)^6219
        have hw : |(44194083/80000000 : ℝ)|=(44194083/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147382281/10000000000 : ℝ)|^8267 ≤ (41362613249881/100000000000000 : ℝ)^6219
        have hw : |(5147382281/10000000000 : ℝ)|=(5147382281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688423967/5000000000 : ℝ)*x 0 + (-237652707/1000000000 : ℝ)*x 1 + (514738319/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688423967/5000000000 : ℝ)^8267 ≤ (43831560633601/100000000000000 : ℝ)^6219 := by
    have hnat : (2688423967 : ℕ)^8267*100000000000000^6219 ≤ 43831560633601^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688423967 5000000000 43831560633601 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237652707/1000000000 : ℝ)^8267 ≤ (14805816390291/100000000000000 : ℝ)^6219 := by
    have hnat : (237652707 : ℕ)^8267*100000000000000^6219 ≤ 14805816390291^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237652707 1000000000 14805816390291 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514738319/1000000000 : ℝ)^8267 ≤ (20681311479869/50000000000000 : ℝ)^6219 := by
    have hnat : (514738319 : ℕ)^8267*50000000000000^6219 ≤ 20681311479869^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514738319 1000000000 20681311479869 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688423967/5000000000 : ℝ), (-237652707/1000000000 : ℝ), (514738319/1000000000 : ℝ)] ![(43831560633601/100000000000000 : ℝ), (14805816390291/100000000000000 : ℝ), (20681311479869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688423967/5000000000 : ℝ)|^8267 ≤ (43831560633601/100000000000000 : ℝ)^6219
        have hw : |(2688423967/5000000000 : ℝ)|=(2688423967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237652707/1000000000 : ℝ)|^8267 ≤ (14805816390291/100000000000000 : ℝ)^6219
        have hw : |(-237652707/1000000000 : ℝ)|=(237652707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514738319/1000000000 : ℝ)|^8267 ≤ (20681311479869/50000000000000 : ℝ)^6219
        have hw : |(514738319/1000000000 : ℝ)|=(514738319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376847267/10000000000 : ℝ)*x 0 + (2573691943/5000000000 : ℝ)*x 1 + (-1188263523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376847267/10000000000 : ℝ)^8267 ≤ (43831553405697/100000000000000 : ℝ)^6219 := by
    have hnat : (5376847267 : ℕ)^8267*100000000000000^6219 ≤ 43831553405697^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376847267 10000000000 43831553405697 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573691943/5000000000 : ℝ)^8267 ≤ (10340657598587/25000000000000 : ℝ)^6219 := by
    have hnat : (2573691943 : ℕ)^8267*25000000000000^6219 ≤ 10340657598587^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573691943 5000000000 10340657598587 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1188263523/5000000000 : ℝ)^8267 ≤ (3701454047883/25000000000000 : ℝ)^6219 := by
    have hnat : (1188263523 : ℕ)^8267*25000000000000^6219 ≤ 3701454047883^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188263523 5000000000 3701454047883 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376847267/10000000000 : ℝ), (2573691943/5000000000 : ℝ), (-1188263523/5000000000 : ℝ)] ![(43831553405697/100000000000000 : ℝ), (10340657598587/25000000000000 : ℝ), (3701454047883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376847267/10000000000 : ℝ)|^8267 ≤ (43831553405697/100000000000000 : ℝ)^6219
        have hw : |(5376847267/10000000000 : ℝ)|=(5376847267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573691943/5000000000 : ℝ)|^8267 ≤ (10340657598587/25000000000000 : ℝ)^6219
        have hw : |(2573691943/5000000000 : ℝ)|=(2573691943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1188263523/5000000000 : ℝ)|^8267 ≤ (3701454047883/25000000000000 : ℝ)^6219
        have hw : |(-1188263523/5000000000 : ℝ)|=(1188263523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090509919/2500000000 : ℝ)*x 0 + (4007925823/10000000000 : ℝ)*x 1 + (2373857317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090509919/2500000000 : ℝ)^8267 ≤ (33192088088923/100000000000000 : ℝ)^6219 := by
    have hnat : (1090509919 : ℕ)^8267*100000000000000^6219 ≤ 33192088088923^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090509919 2500000000 33192088088923 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007925823/10000000000 : ℝ)^8267 ≤ (5931790460297/20000000000000 : ℝ)^6219 := by
    have hnat : (4007925823 : ℕ)^8267*20000000000000^6219 ≤ 5931790460297^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007925823 10000000000 5931790460297 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373857317/5000000000 : ℝ)^8267 ≤ (37148959594433/100000000000000 : ℝ)^6219 := by
    have hnat : (2373857317 : ℕ)^8267*100000000000000^6219 ≤ 37148959594433^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373857317 5000000000 37148959594433 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090509919/2500000000 : ℝ), (4007925823/10000000000 : ℝ), (2373857317/5000000000 : ℝ)] ![(33192088088923/100000000000000 : ℝ), (5931790460297/20000000000000 : ℝ), (37148959594433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090509919/2500000000 : ℝ)|^8267 ≤ (33192088088923/100000000000000 : ℝ)^6219
        have hw : |(1090509919/2500000000 : ℝ)|=(1090509919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007925823/10000000000 : ℝ)|^8267 ≤ (5931790460297/20000000000000 : ℝ)^6219
        have hw : |(4007925823/10000000000 : ℝ)|=(4007925823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2373857317/5000000000 : ℝ)|^8267 ≤ (37148959594433/100000000000000 : ℝ)^6219
        have hw : |(2373857317/5000000000 : ℝ)|=(2373857317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180172459/10000000000 : ℝ)*x 0 + (5150110627/10000000000 : ℝ)*x 1 + (5521503867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180172459/10000000000 : ℝ)^8267 ≤ (13202221814731/100000000000000 : ℝ)^6219 := by
    have hnat : (2180172459 : ℕ)^8267*100000000000000^6219 ≤ 13202221814731^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180172459 10000000000 13202221814731 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150110627/10000000000 : ℝ)^8267 ≤ (41391759740381/100000000000000 : ℝ)^6219 := by
    have hnat : (5150110627 : ℕ)^8267*100000000000000^6219 ≤ 41391759740381^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150110627 10000000000 41391759740381 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5521503867/10000000000 : ℝ)^8267 ≤ (9081203686609/20000000000000 : ℝ)^6219 := by
    have hnat : (5521503867 : ℕ)^8267*20000000000000^6219 ≤ 9081203686609^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521503867 10000000000 9081203686609 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180172459/10000000000 : ℝ), (5150110627/10000000000 : ℝ), (5521503867/10000000000 : ℝ)] ![(13202221814731/100000000000000 : ℝ), (41391759740381/100000000000000 : ℝ), (9081203686609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180172459/10000000000 : ℝ)|^8267 ≤ (13202221814731/100000000000000 : ℝ)^6219
        have hw : |(-2180172459/10000000000 : ℝ)|=(2180172459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150110627/10000000000 : ℝ)|^8267 ≤ (41391759740381/100000000000000 : ℝ)^6219
        have hw : |(5150110627/10000000000 : ℝ)|=(5150110627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5521503867/10000000000 : ℝ)|^8267 ≤ (9081203686609/20000000000000 : ℝ)^6219
        have hw : |(5521503867/10000000000 : ℝ)|=(5521503867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660208187/1250000000 : ℝ)*x 0 + (-125150559/625000000 : ℝ)*x 1 + (2760751979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660208187/1250000000 : ℝ)^8267 ≤ (42803140443363/100000000000000 : ℝ)^6219 := by
    have hnat : (660208187 : ℕ)^8267*100000000000000^6219 ≤ 42803140443363^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660208187 1250000000 42803140443363 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125150559/625000000 : ℝ)^8267 ≤ (1179084011707/10000000000000 : ℝ)^6219 := by
    have hnat : (125150559 : ℕ)^8267*10000000000000^6219 ≤ 1179084011707^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125150559 625000000 1179084011707 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760751979/5000000000 : ℝ)^8267 ≤ (2270300971391/5000000000000 : ℝ)^6219 := by
    have hnat : (2760751979 : ℕ)^8267*5000000000000^6219 ≤ 2270300971391^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760751979 5000000000 2270300971391 5000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660208187/1250000000 : ℝ), (-125150559/625000000 : ℝ), (2760751979/5000000000 : ℝ)] ![(42803140443363/100000000000000 : ℝ), (1179084011707/10000000000000 : ℝ), (2270300971391/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660208187/1250000000 : ℝ)|^8267 ≤ (42803140443363/100000000000000 : ℝ)^6219
        have hw : |(660208187/1250000000 : ℝ)|=(660208187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125150559/625000000 : ℝ)|^8267 ≤ (1179084011707/10000000000000 : ℝ)^6219
        have hw : |(-125150559/625000000 : ℝ)|=(125150559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760751979/5000000000 : ℝ)|^8267 ≤ (2270300971391/5000000000000 : ℝ)^6219
        have hw : |(2760751979/5000000000 : ℝ)|=(2760751979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281665739/10000000000 : ℝ)*x 0 + (2760751899/5000000000 : ℝ)*x 1 + (-2002408833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281665739/10000000000 : ℝ)^8267 ≤ (1712125722447/4000000000000 : ℝ)^6219 := by
    have hnat : (5281665739 : ℕ)^8267*4000000000000^6219 ≤ 1712125722447^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281665739 10000000000 1712125722447 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760751899/5000000000 : ℝ)^8267 ≤ (9081203535753/20000000000000 : ℝ)^6219 := by
    have hnat : (2760751899 : ℕ)^8267*20000000000000^6219 ≤ 9081203535753^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760751899 5000000000 9081203535753 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002408833/10000000000 : ℝ)^8267 ≤ (471633569929/4000000000000 : ℝ)^6219 := by
    have hnat : (2002408833 : ℕ)^8267*4000000000000^6219 ≤ 471633569929^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002408833 10000000000 471633569929 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281665739/10000000000 : ℝ), (2760751899/5000000000 : ℝ), (-2002408833/10000000000 : ℝ)] ![(1712125722447/4000000000000 : ℝ), (9081203535753/20000000000000 : ℝ), (471633569929/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281665739/10000000000 : ℝ)|^8267 ≤ (1712125722447/4000000000000 : ℝ)^6219
        have hw : |(5281665739/10000000000 : ℝ)|=(5281665739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760751899/5000000000 : ℝ)|^8267 ≤ (9081203535753/20000000000000 : ℝ)^6219
        have hw : |(2760751899/5000000000 : ℝ)|=(2760751899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002408833/10000000000 : ℝ)|^8267 ≤ (471633569929/4000000000000 : ℝ)^6219
        have hw : |(-2002408833/10000000000 : ℝ)|=(2002408833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362277719/10000000000 : ℝ)*x 0 + (4742367869/10000000000 : ℝ)*x 1 + (2006666147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362277719/10000000000 : ℝ)^8267 ≤ (33194495951301/100000000000000 : ℝ)^6219 := by
    have hnat : (4362277719 : ℕ)^8267*100000000000000^6219 ≤ 33194495951301^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362277719 10000000000 33194495951301 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4742367869/10000000000 : ℝ)^8267 ≤ (4636669546441/12500000000000 : ℝ)^6219 := by
    have hnat : (4742367869 : ℕ)^8267*12500000000000^6219 ≤ 4636669546441^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742367869 10000000000 4636669546441 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006666147/5000000000 : ℝ)^8267 ≤ (29712147668743/100000000000000 : ℝ)^6219 := by
    have hnat : (2006666147 : ℕ)^8267*100000000000000^6219 ≤ 29712147668743^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006666147 5000000000 29712147668743 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362277719/10000000000 : ℝ), (4742367869/10000000000 : ℝ), (2006666147/5000000000 : ℝ)] ![(33194495951301/100000000000000 : ℝ), (4636669546441/12500000000000 : ℝ), (29712147668743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362277719/10000000000 : ℝ)|^8267 ≤ (33194495951301/100000000000000 : ℝ)^6219
        have hw : |(4362277719/10000000000 : ℝ)|=(4362277719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4742367869/10000000000 : ℝ)|^8267 ≤ (4636669546441/12500000000000 : ℝ)^6219
        have hw : |(4742367869/10000000000 : ℝ)|=(4742367869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006666147/5000000000 : ℝ)|^8267 ≤ (29712147668743/100000000000000 : ℝ)^6219
        have hw : |(2006666147/5000000000 : ℝ)|=(2006666147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_8 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-20076817/2000000000 : ℝ)*x 0 + (2963467531/5000000000 : ℝ)*x 1 + (5926746859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20076817/2000000000 : ℝ)^8267 ≤ (22059026283/10000000000000 : ℝ)^6219 := by
    have hnat : (20076817 : ℕ)^8267*10000000000000^6219 ≤ 22059026283^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20076817 2000000000 22059026283 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963467531/5000000000 : ℝ)^8267 ≤ (49890757823729/100000000000000 : ℝ)^6219 := by
    have hnat : (2963467531 : ℕ)^8267*100000000000000^6219 ≤ 49890757823729^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963467531 5000000000 49890757823729 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5926746859/10000000000 : ℝ)^8267 ≤ (6236081488139/12500000000000 : ℝ)^6219 := by
    have hnat : (5926746859 : ℕ)^8267*12500000000000^6219 ≤ 6236081488139^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926746859 10000000000 6236081488139 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20076817/2000000000 : ℝ), (2963467531/5000000000 : ℝ), (5926746859/10000000000 : ℝ)] ![(22059026283/10000000000000 : ℝ), (49890757823729/100000000000000 : ℝ), (6236081488139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20076817/2000000000 : ℝ)|^8267 ≤ (22059026283/10000000000000 : ℝ)^6219
        have hw : |(-20076817/2000000000 : ℝ)|=(20076817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963467531/5000000000 : ℝ)|^8267 ≤ (49890757823729/100000000000000 : ℝ)^6219
        have hw : |(2963467531/5000000000 : ℝ)|=(2963467531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5926746859/10000000000 : ℝ)|^8267 ≤ (6236081488139/12500000000000 : ℝ)^6219
        have hw : |(5926746859/10000000000 : ℝ)|=(5926746859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_9 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (796244653/10000000000 : ℝ)*x 0 + (-2482363577/5000000000 : ℝ)*x 1 + (65617423/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796244653/10000000000 : ℝ)^8267 ≤ (3460560378697/100000000000000 : ℝ)^6219 := by
    have hnat : (796244653 : ℕ)^8267*100000000000000^6219 ≤ 3460560378697^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796244653 10000000000 3460560378697 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482363577/5000000000 : ℝ)^8267 ≤ (3942299939153/10000000000000 : ℝ)^6219 := by
    have hnat : (2482363577 : ℕ)^8267*10000000000000^6219 ≤ 3942299939153^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482363577 5000000000 3942299939153 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65617423/100000000 : ℝ)^8267 ≤ (57116440209419/100000000000000 : ℝ)^6219 := by
    have hnat : (65617423 : ℕ)^8267*100000000000000^6219 ≤ 57116440209419^6219*100000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65617423 100000000 57116440209419 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796244653/10000000000 : ℝ), (-2482363577/5000000000 : ℝ), (65617423/100000000 : ℝ)] ![(3460560378697/100000000000000 : ℝ), (3942299939153/10000000000000 : ℝ), (57116440209419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796244653/10000000000 : ℝ)|^8267 ≤ (3460560378697/100000000000000 : ℝ)^6219
        have hw : |(796244653/10000000000 : ℝ)|=(796244653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2482363577/5000000000 : ℝ)|^8267 ≤ (3942299939153/10000000000000 : ℝ)^6219
        have hw : |(-2482363577/5000000000 : ℝ)|=(2482363577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65617423/100000000 : ℝ)|^8267 ≤ (57116440209419/100000000000000 : ℝ)^6219
        have hw : |(65617423/100000000 : ℝ)|=(65617423/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_10 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (158976109/2000000000 : ℝ)*x 0 + (327911631/500000000 : ℝ)*x 1 + (-4969319809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158976109/2000000000 : ℝ)^8267 ≤ (3452681698613/100000000000000 : ℝ)^6219 := by
    have hnat : (158976109 : ℕ)^8267*100000000000000^6219 ≤ 3452681698613^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158976109 2000000000 3452681698613 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327911631/500000000 : ℝ)^8267 ≤ (3567239589009/6250000000000 : ℝ)^6219 := by
    have hnat : (327911631 : ℕ)^8267*6250000000000^6219 ≤ 3567239589009^6219*500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327911631 500000000 3567239589009 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4969319809/10000000000 : ℝ)^8267 ≤ (7894296972359/20000000000000 : ℝ)^6219 := by
    have hnat : (4969319809 : ℕ)^8267*20000000000000^6219 ≤ 7894296972359^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4969319809 10000000000 7894296972359 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(158976109/2000000000 : ℝ), (327911631/500000000 : ℝ), (-4969319809/10000000000 : ℝ)] ![(3452681698613/100000000000000 : ℝ), (3567239589009/6250000000000 : ℝ), (7894296972359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(158976109/2000000000 : ℝ)|^8267 ≤ (3452681698613/100000000000000 : ℝ)^6219
        have hw : |(158976109/2000000000 : ℝ)|=(158976109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327911631/500000000 : ℝ)|^8267 ≤ (3567239589009/6250000000000 : ℝ)^6219
        have hw : |(327911631/500000000 : ℝ)|=(327911631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4969319809/10000000000 : ℝ)|^8267 ≤ (7894296972359/20000000000000 : ℝ)^6219
        have hw : |(-4969319809/10000000000 : ℝ)|=(4969319809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s2_11 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (104879067/2500000000 : ℝ)*x 0 + (5868701987/10000000000 : ℝ)*x 1 + (73407183/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104879067/2500000000 : ℝ)^8267 ≤ (1476391516597/100000000000000 : ℝ)^6219 := by
    have hnat : (104879067 : ℕ)^8267*100000000000000^6219 ≤ 1476391516597^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104879067 2500000000 1476391516597 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5868701987/10000000000 : ℝ)^8267 ≤ (24620102682123/50000000000000 : ℝ)^6219 := by
    have hnat : (5868701987 : ℕ)^8267*50000000000000^6219 ≤ 24620102682123^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5868701987 10000000000 24620102682123 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73407183/125000000 : ℝ)^8267 ≤ (12320850773991/25000000000000 : ℝ)^6219 := by
    have hnat : (73407183 : ℕ)^8267*25000000000000^6219 ≤ 12320850773991^6219*125000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73407183 125000000 12320850773991 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104879067/2500000000 : ℝ), (5868701987/10000000000 : ℝ), (73407183/125000000 : ℝ)] ![(1476391516597/100000000000000 : ℝ), (24620102682123/50000000000000 : ℝ), (12320850773991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104879067/2500000000 : ℝ)|^8267 ≤ (1476391516597/100000000000000 : ℝ)^6219
        have hw : |(104879067/2500000000 : ℝ)|=(104879067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5868701987/10000000000 : ℝ)|^8267 ≤ (24620102682123/50000000000000 : ℝ)^6219
        have hw : |(5868701987/10000000000 : ℝ)|=(5868701987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73407183/125000000 : ℝ)|^8267 ≤ (12320850773991/25000000000000 : ℝ)^6219
        have hw : |(73407183/125000000 : ℝ)|=(73407183/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (263/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (8751/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3343/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (263/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (263/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (263/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (263/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (263/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (263/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (263/5000 : ℝ) ^ (4133/1024 : ℝ) ≤ (86027758512343/12500000000000000000 : ℝ) := by
    have hpowers : (263/5000 : ℝ)^4133 ≤ (86027758512343/12500000000000000000 : ℝ)^1024 := by
      have hnat : (263 : ℕ)^4133*12500000000000000000^1024 ≤ 86027758512343^1024*5000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        263 5000 86027758512343 12500000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (263/5000 : ℝ)) (X := (86027758512343/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20753/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (87622927778476087/50000000000000000000 : ℝ) := by
    have hpowers : (20753/100000 : ℝ)^4133 ≤ (87622927778476087/50000000000000000000 : ℝ)^1024 := by
      have hnat : (20753 : ℕ)^4133*50000000000000000000^1024 ≤ 87622927778476087^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20753 100000 87622927778476087 50000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20753/100000 : ℝ)) (X := (87622927778476087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250086027758512343/6250000000000000000 : ℝ) ≤ (2500008525716783/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (6250086027758512343/6250000000000000000 : ℝ)^1024 ≤ (2500008525716783/2500000000000000 : ℝ)^4133 := by
      have hnat : (6250086027758512343 : ℕ)^1024*2500000000000000^4133 ≤ 2500008525716783^4133*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250086027758512343 6250000000000000000 2500008525716783 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008525716783/2500000000000000 : ℝ)) (X := (6250086027758512343/6250000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50087967038812525459/50000000000000000000 : ℝ) ≤ (10004356094952929/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50087967038812525459/50000000000000000000 : ℝ)^1024 ≤ (10004356094952929/10000000000000000 : ℝ)^4133 := by
      have hnat : (50087967038812525459 : ℕ)^1024*10000000000000000^4133 ≤ 10004356094952929^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50087967038812525459 50000000000000000000 10004356094952929 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004356094952929/10000000000000000 : ℝ)) (X := (50087967038812525459/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25087622927778476087/25000000000000000000 : ℝ) ≤ (5004339043519363/5000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (25087622927778476087/25000000000000000000 : ℝ)^1024 ≤ (5004339043519363/5000000000000000 : ℝ)^4133 := by
      have hnat : (25087622927778476087 : ℕ)^1024*5000000000000000^4133 ≤ 5004339043519363^4133*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25087622927778476087 25000000000000000000 5004339043519363 5000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004339043519363/5000000000000000 : ℝ)) (X := (25087622927778476087/25000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(86027758512343/12500000000000000000 : ℝ) ≤ ((38721265249744472909/38732500000000000000 : ℝ)+2*(4321992085797/1549300000000000 : ℝ)*(263/5000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (38721265249744472909/38732500000000000000 : ℝ)+2*(4321992085797/1549300000000000 : ℝ)*(263/5000 : ℝ)=(2500008525716783/2500000000000000 : ℝ) by norm_num, show 1+2*(86027758512343/12500000000000000000 : ℝ)=(6250086027758512343/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(87622927778476087/50000000000000000000 : ℝ)+(86027758512343/12500000000000000000 : ℝ) ≤ ((38721265249744472909/38732500000000000000 : ℝ)+(4321992085797/1549300000000000 : ℝ)*((20753/100000 : ℝ)+(263/5000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (38721265249744472909/38732500000000000000 : ℝ)+(4321992085797/1549300000000000 : ℝ)*((20753/100000 : ℝ)+(263/5000 : ℝ))=(10004356094952929/10000000000000000 : ℝ) by norm_num, show 1+(87622927778476087/50000000000000000000 : ℝ)+(86027758512343/12500000000000000000 : ℝ)=(50087967038812525459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(87622927778476087/50000000000000000000 : ℝ) ≤ ((38721265249744472909/38732500000000000000 : ℝ)+2*(4321992085797/1549300000000000 : ℝ)*(20753/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (38721265249744472909/38732500000000000000 : ℝ)+2*(4321992085797/1549300000000000 : ℝ)*(20753/100000 : ℝ)=(5004339043519363/5000000000000000 : ℝ) by norm_num, show 1+2*(87622927778476087/50000000000000000000 : ℝ)=(25087622927778476087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38721265249744472909/38732500000000000000 : ℝ)*(X 1 0+X 2 0)+(4321992085797/1549300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (263/5000 : ℝ)) (hi := (20753/100000 : ℝ)) (c := (38721265249744472909/38732500000000000000 : ℝ)) (alpha := (4321992085797/1549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38721265249744472909/38732500000000000000 : ℝ)*(X 0 1+X 2 1)+(4321992085797/1549300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (263/5000 : ℝ)) (hi := (20753/100000 : ℝ)) (c := (38721265249744472909/38732500000000000000 : ℝ)) (alpha := (4321992085797/1549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38721265249744472909/38732500000000000000 : ℝ)*(X 0 2+X 1 2)+(4321992085797/1549300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (263/5000 : ℝ)) (hi := (20753/100000 : ℝ)) (c := (38721265249744472909/38732500000000000000 : ℝ)) (alpha := (4321992085797/1549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436009919/2000000000 : ℝ)*X 0 0+(44194083/80000000 : ℝ)*X 0 1+(5147382281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688423967/5000000000 : ℝ)*X 1 0+(-237652707/1000000000 : ℝ)*X 1 1+(514738319/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376847267/10000000000 : ℝ)*X 2 0+(2573691943/5000000000 : ℝ)*X 2 1+(-1188263523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090509919/2500000000 : ℝ)*X 0 0+(4007925823/10000000000 : ℝ)*X 0 1+(2373857317/5000000000 : ℝ)*X 0 2+(1090509919/2500000000 : ℝ)*X 1 0+(4007925823/10000000000 : ℝ)*X 1 1+(2373857317/5000000000 : ℝ)*X 1 2+(1090509919/2500000000 : ℝ)*X 2 0+(4007925823/10000000000 : ℝ)*X 2 1+(2373857317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180172459/10000000000 : ℝ)*X 0 0+(5150110627/10000000000 : ℝ)*X 0 1+(5521503867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660208187/1250000000 : ℝ)*X 1 0+(-125150559/625000000 : ℝ)*X 1 1+(2760751979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281665739/10000000000 : ℝ)*X 2 0+(2760751899/5000000000 : ℝ)*X 2 1+(-2002408833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362277719/10000000000 : ℝ)*X 0 0+(4742367869/10000000000 : ℝ)*X 0 1+(2006666147/5000000000 : ℝ)*X 0 2+(4362277719/10000000000 : ℝ)*X 1 0+(4742367869/10000000000 : ℝ)*X 1 1+(2006666147/5000000000 : ℝ)*X 1 2+(4362277719/10000000000 : ℝ)*X 2 0+(4742367869/10000000000 : ℝ)*X 2 1+(2006666147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-20076817/2000000000 : ℝ)*X 0 0+(2963467531/5000000000 : ℝ)*X 0 1+(5926746859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((796244653/10000000000 : ℝ)*X 1 0+(-2482363577/5000000000 : ℝ)*X 1 1+(65617423/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((158976109/2000000000 : ℝ)*X 2 0+(327911631/500000000 : ℝ)*X 2 1+(-4969319809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((104879067/2500000000 : ℝ)*X 0 0+(5868701987/10000000000 : ℝ)*X 0 1+(73407183/125000000 : ℝ)*X 0 2+(104879067/2500000000 : ℝ)*X 1 0+(5868701987/10000000000 : ℝ)*X 1 1+(73407183/125000000 : ℝ)*X 1 2+(104879067/2500000000 : ℝ)*X 2 0+(5868701987/10000000000 : ℝ)*X 2 1+(73407183/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9664587476268334367601/3873250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8010336064479/400000000000 : ℝ)*(major0) + (8010336064479/400000000000 : ℝ)*(major1) + (8010336064479/400000000000 : ℝ)*(major2) + (1326701373272143/50000000000000 : ℝ)*(sp0) + (2653412528496571/100000000000000 : ℝ)*(sp1) + (1326707948760349/50000000000000 : ℝ)*(sp2) + (135173744585781/10000000000000 : ℝ)*(sp3) + (24569963853/100000000000000 : ℝ)*(sp4) + (1803475407/12500000000000 : ℝ)*(sp5) + (2845572317/25000000000000 : ℝ)*(sp6) + (171848413/12500000000000 : ℝ)*(sp8) + (346999123/20000000000000 : ℝ)*(sp9) + (352871369/25000000000000 : ℝ)*(sp10) + (905956223/50000000000000 : ℝ)*(sp11) + (84483703610641/6250000000000 : ℝ)*(f.failure) + (1326714345647721/50000000000000 : ℝ)*(f.sum) + (20328065333493/15493000000000000000000000000 : ℝ)*base66 + (37858990377398589/15493000000000000000000000000000 : ℝ)*base68 + (63639517014494589/15493000000000000000000000000000 : ℝ)*base70 + (72645163180914589/15493000000000000000000000000000 : ℝ)*base72 + (12969303209717/7746500000000000000000000000 : ℝ)*base74 + (58068081062300411/15493000000000000000000000000000 : ℝ)*base75 + (18741847347256411/15493000000000000000000000000000 : ℝ)*base77 + (20254424010482411/15493000000000000000000000000000 : ℝ)*base79 + (14237682528979/7746500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (320931/625000000000000000000 : ℝ)*base89 + (320931/625000000000000000000 : ℝ)*base91 + (320931/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12613033802836708649941658829/968312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1016060755394709/50000000000000 : ℝ)*(major0) + (1016060755394709/50000000000000 : ℝ)*(major1) + (1016060755394709/50000000000000 : ℝ)*(major2) + (257702793/25000000000000 : ℝ)*(sp1) + (2000199/400000000000 : ℝ)*(sp2) + (335124247/100000000000000 : ℝ)*(sp3) + (1346282037601301/50000000000000 : ℝ)*(sp4) + (1346281918094947/50000000000000 : ℝ)*(sp5) + (2692564232605181/100000000000000 : ℝ)*(sp6) + (685837825768689/50000000000000 : ℝ)*(sp7) + (303713569/20000000000000 : ℝ)*(sp8) + (726769381/100000000000000 : ℝ)*(sp9) + (172223103/20000000000000 : ℝ)*(sp10) + (1006953809/100000000000000 : ℝ)*(sp11) + (1371676993615433/100000000000000 : ℝ)*(f.failure) + (1346282796885223/50000000000000 : ℝ)*(f.sum) + (35294950131549/77465000000000000000000000000 : ℝ)*base66 + (13332174760266986519/1936625000000000000000000000000000 : ℝ)*base68 + (9264373715414111519/1936625000000000000000000000000000 : ℝ)*base70 + (1626567087906111519/1936625000000000000000000000000000 : ℝ)*base72 + (22767480568503/38732500000000000000000000000 : ℝ)*base73 + (10322748269663986519/1936625000000000000000000000000000 : ℝ)*base76 + (431469640001986519/1936625000000000000000000000000000 : ℝ)*base78 + (4502854260297236519/1936625000000000000000000000000000 : ℝ)*base80 + (97418447022121/19366250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (43651797/10000000000000000000000 : ℝ)*base90 + (43651797/10000000000000000000000 : ℝ)*base92 + (43651797/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1074_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (263/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1074_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1074_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1074_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1074_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
