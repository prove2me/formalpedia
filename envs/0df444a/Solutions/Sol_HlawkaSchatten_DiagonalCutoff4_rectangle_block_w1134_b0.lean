-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:28:25.904389+00:00
-- url     : https://prove2.me/submissions/34d9d5fd-fcae-46fe-ba99-a1902042dc7f

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
theorem support_rectangle_w1134_s0_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-947172827/5000000000 : ℝ)*x 0 + (3028090431/5000000000 : ℝ)*x 1 + (4779459621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947172827/5000000000 : ℝ)^8327 ≤ (5505041179943/50000000000000 : ℝ)^6279 := by
    have hnat : (947172827 : ℕ)^8327*50000000000000^6279 ≤ 5505041179943^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947172827 5000000000 5505041179943 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3028090431/5000000000 : ℝ)^8327 ≤ (51423232629553/100000000000000 : ℝ)^6279 := by
    have hnat : (3028090431 : ℕ)^8327*100000000000000^6279 ≤ 51423232629553^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028090431 5000000000 51423232629553 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779459621/10000000000 : ℝ)^8327 ≤ (37566685000853/100000000000000 : ℝ)^6279 := by
    have hnat : (4779459621 : ℕ)^8327*100000000000000^6279 ≤ 37566685000853^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779459621 10000000000 37566685000853 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947172827/5000000000 : ℝ), (3028090431/5000000000 : ℝ), (4779459621/10000000000 : ℝ)] ![(5505041179943/50000000000000 : ℝ), (51423232629553/100000000000000 : ℝ), (37566685000853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947172827/5000000000 : ℝ)|^8327 ≤ (5505041179943/50000000000000 : ℝ)^6279
        have hw : |(-947172827/5000000000 : ℝ)|=(947172827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3028090431/5000000000 : ℝ)|^8327 ≤ (51423232629553/100000000000000 : ℝ)^6279
        have hw : |(3028090431/5000000000 : ℝ)|=(3028090431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779459621/10000000000 : ℝ)|^8327 ≤ (37566685000853/100000000000000 : ℝ)^6279
        have hw : |(4779459621/10000000000 : ℝ)|=(4779459621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2758621649/5000000000 : ℝ)*x 0 + (-1313631781/5000000000 : ℝ)*x 1 + (1194865007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758621649/5000000000 : ℝ)^8327 ≤ (22722207977799/50000000000000 : ℝ)^6279 := by
    have hnat : (2758621649 : ℕ)^8327*50000000000000^6279 ≤ 22722207977799^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758621649 5000000000 22722207977799 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313631781/5000000000 : ℝ)^8327 ≤ (16988894791307/100000000000000 : ℝ)^6279 := by
    have hnat : (1313631781 : ℕ)^8327*100000000000000^6279 ≤ 16988894791307^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313631781 5000000000 16988894791307 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194865007/2500000000 : ℝ)^8327 ≤ (37566689243301/100000000000000 : ℝ)^6279 := by
    have hnat : (1194865007 : ℕ)^8327*100000000000000^6279 ≤ 37566689243301^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194865007 2500000000 37566689243301 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758621649/5000000000 : ℝ), (-1313631781/5000000000 : ℝ), (1194865007/2500000000 : ℝ)] ![(22722207977799/50000000000000 : ℝ), (16988894791307/100000000000000 : ℝ), (37566689243301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758621649/5000000000 : ℝ)|^8327 ≤ (22722207977799/50000000000000 : ℝ)^6279
        have hw : |(2758621649/5000000000 : ℝ)|=(2758621649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1313631781/5000000000 : ℝ)|^8327 ≤ (16988894791307/100000000000000 : ℝ)^6279
        have hw : |(-1313631781/5000000000 : ℝ)|=(1313631781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194865007/2500000000 : ℝ)|^8327 ≤ (37566689243301/100000000000000 : ℝ)^6279
        have hw : |(1194865007/2500000000 : ℝ)|=(1194865007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689655761/1250000000 : ℝ)*x 0 + (597432361/1250000000 : ℝ)*x 1 + (-2627261393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689655761/1250000000 : ℝ)^8327 ≤ (45444446431791/100000000000000 : ℝ)^6279 := by
    have hnat : (689655761 : ℕ)^8327*100000000000000^6279 ≤ 45444446431791^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689655761 1250000000 45444446431791 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597432361/1250000000 : ℝ)^8327 ≤ (37566677360277/100000000000000 : ℝ)^6279 := by
    have hnat : (597432361 : ℕ)^8327*100000000000000^6279 ≤ 37566677360277^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597432361 1250000000 37566677360277 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627261393/10000000000 : ℝ)^8327 ≤ (3397775238209/20000000000000 : ℝ)^6279 := by
    have hnat : (2627261393 : ℕ)^8327*20000000000000^6279 ≤ 3397775238209^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627261393 10000000000 3397775238209 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689655761/1250000000 : ℝ), (597432361/1250000000 : ℝ), (-2627261393/10000000000 : ℝ)] ![(45444446431791/100000000000000 : ℝ), (37566677360277/100000000000000 : ℝ), (3397775238209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689655761/1250000000 : ℝ)|^8327 ≤ (45444446431791/100000000000000 : ℝ)^6279
        have hw : |(689655761/1250000000 : ℝ)|=(689655761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597432361/1250000000 : ℝ)|^8327 ≤ (37566677360277/100000000000000 : ℝ)^6279
        have hw : |(597432361/1250000000 : ℝ)|=(597432361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2627261393/10000000000 : ℝ)|^8327 ≤ (3397775238209/20000000000000 : ℝ)^6279
        have hw : |(-2627261393/10000000000 : ℝ)|=(2627261393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4201639043/10000000000 : ℝ)*x 0 + (195090723/625000000 : ℝ)*x 1 + (1131494213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201639043/10000000000 : ℝ)^8327 ≤ (6333160747753/20000000000000 : ℝ)^6279 := by
    have hnat : (4201639043 : ℕ)^8327*20000000000000^6279 ≤ 6333160747753^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201639043 10000000000 6333160747753 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195090723/625000000 : ℝ)^8327 ≤ (5337926970327/25000000000000 : ℝ)^6279 := by
    have hnat : (195090723 : ℕ)^8327*25000000000000^6279 ≤ 5337926970327^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195090723 625000000 5337926970327 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131494213/2000000000 : ℝ)^8327 ≤ (46982488361017/100000000000000 : ℝ)^6279 := by
    have hnat : (1131494213 : ℕ)^8327*100000000000000^6279 ≤ 46982488361017^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131494213 2000000000 46982488361017 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201639043/10000000000 : ℝ), (195090723/625000000 : ℝ), (1131494213/2000000000 : ℝ)] ![(6333160747753/20000000000000 : ℝ), (5337926970327/25000000000000 : ℝ), (46982488361017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201639043/10000000000 : ℝ)|^8327 ≤ (6333160747753/20000000000000 : ℝ)^6279
        have hw : |(4201639043/10000000000 : ℝ)|=(4201639043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195090723/625000000 : ℝ)|^8327 ≤ (5337926970327/25000000000000 : ℝ)^6279
        have hw : |(195090723/625000000 : ℝ)|=(195090723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131494213/2000000000 : ℝ)|^8327 ≤ (46982488361017/100000000000000 : ℝ)^6279
        have hw : |(1131494213/2000000000 : ℝ)|=(1131494213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-474878611/2500000000 : ℝ)*x 0 + (2406199687/5000000000 : ℝ)*x 1 + (120441677/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474878611/2500000000 : ℝ)^8327 ≤ (5524969991749/50000000000000 : ℝ)^6279 := by
    have hnat : (474878611 : ℕ)^8327*50000000000000^6279 ≤ 5524969991749^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474878611 2500000000 5524969991749 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406199687/5000000000 : ℝ)^8327 ≤ (37910424626283/100000000000000 : ℝ)^6279 := by
    have hnat : (2406199687 : ℕ)^8327*100000000000000^6279 ≤ 37910424626283^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406199687 5000000000 37910424626283 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120441677/200000000 : ℝ)^8327 ≤ (5103963537249/10000000000000 : ℝ)^6279 := by
    have hnat : (120441677 : ℕ)^8327*10000000000000^6279 ≤ 5103963537249^6279*200000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120441677 200000000 5103963537249 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474878611/2500000000 : ℝ), (2406199687/5000000000 : ℝ), (120441677/200000000 : ℝ)] ![(5524969991749/50000000000000 : ℝ), (37910424626283/100000000000000 : ℝ), (5103963537249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474878611/2500000000 : ℝ)|^8327 ≤ (5524969991749/50000000000000 : ℝ)^6279
        have hw : |(-474878611/2500000000 : ℝ)|=(474878611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406199687/5000000000 : ℝ)|^8327 ≤ (37910424626283/100000000000000 : ℝ)^6279
        have hw : |(2406199687/5000000000 : ℝ)|=(2406199687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120441677/200000000 : ℝ)|^8327 ≤ (5103963537249/10000000000000 : ℝ)^6279
        have hw : |(120441677/200000000 : ℝ)|=(120441677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292592523/2500000000 : ℝ)*x 0 + (-1384638601/10000000000 : ℝ)*x 1 + (4817667/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292592523/2500000000 : ℝ)^8327 ≤ (41694806126699/100000000000000 : ℝ)^6279 := by
    have hnat : (1292592523 : ℕ)^8327*100000000000000^6279 ≤ 41694806126699^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292592523 2500000000 41694806126699 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384638601/10000000000 : ℝ)^8327 ≤ (290622384363/4000000000000 : ℝ)^6279 := by
    have hnat : (1384638601 : ℕ)^8327*4000000000000^6279 ≤ 290622384363^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384638601 10000000000 290622384363 4000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817667/8000000 : ℝ)^8327 ≤ (51039634248509/100000000000000 : ℝ)^6279 := by
    have hnat : (4817667 : ℕ)^8327*100000000000000^6279 ≤ 51039634248509^6279*8000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817667 8000000 51039634248509 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292592523/2500000000 : ℝ), (-1384638601/10000000000 : ℝ), (4817667/8000000 : ℝ)] ![(41694806126699/100000000000000 : ℝ), (290622384363/4000000000000 : ℝ), (51039634248509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292592523/2500000000 : ℝ)|^8327 ≤ (41694806126699/100000000000000 : ℝ)^6279
        have hw : |(1292592523/2500000000 : ℝ)|=(1292592523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1384638601/10000000000 : ℝ)|^8327 ≤ (290622384363/4000000000000 : ℝ)^6279
        have hw : |(-1384638601/10000000000 : ℝ)|=(1384638601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817667/8000000 : ℝ)|^8327 ≤ (51039634248509/100000000000000 : ℝ)^6279
        have hw : |(4817667/8000000 : ℝ)|=(4817667/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170370109/10000000000 : ℝ)*x 0 + (3011041877/5000000000 : ℝ)*x 1 + (-1384638567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170370109/10000000000 : ℝ)^8327 ≤ (5211850788563/12500000000000 : ℝ)^6279 := by
    have hnat : (5170370109 : ℕ)^8327*12500000000000^6279 ≤ 5211850788563^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170370109 10000000000 5211850788563 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3011041877/5000000000 : ℝ)^8327 ≤ (12759908573367/25000000000000 : ℝ)^6279 := by
    have hnat : (3011041877 : ℕ)^8327*25000000000000^6279 ≤ 12759908573367^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011041877 5000000000 12759908573367 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384638567/10000000000 : ℝ)^8327 ≤ (3632779686239/50000000000000 : ℝ)^6279 := by
    have hnat : (1384638567 : ℕ)^8327*50000000000000^6279 ≤ 3632779686239^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384638567 10000000000 3632779686239 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170370109/10000000000 : ℝ), (3011041877/5000000000 : ℝ), (-1384638567/10000000000 : ℝ)] ![(5211850788563/12500000000000 : ℝ), (12759908573367/25000000000000 : ℝ), (3632779686239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170370109/10000000000 : ℝ)|^8327 ≤ (5211850788563/12500000000000 : ℝ)^6279
        have hw : |(5170370109/10000000000 : ℝ)|=(5170370109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3011041877/5000000000 : ℝ)|^8327 ≤ (12759908573367/25000000000000 : ℝ)^6279
        have hw : |(3011041877/5000000000 : ℝ)|=(3011041877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1384638567/10000000000 : ℝ)|^8327 ≤ (3632779686239/50000000000000 : ℝ)^6279
        have hw : |(-1384638567/10000000000 : ℝ)|=(1384638567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s0_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4211906537/10000000000 : ℝ)*x 0 + (5592041107/10000000000 : ℝ)*x 1 + (3189181233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211906537/10000000000 : ℝ)^8327 ≤ (15884232578871/50000000000000 : ℝ)^6279 := by
    have hnat : (4211906537 : ℕ)^8327*50000000000000^6279 ≤ 15884232578871^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211906537 10000000000 15884232578871 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5592041107/10000000000 : ℝ)^8327 ≤ (4626326073629/10000000000000 : ℝ)^6279 := by
    have hnat : (5592041107 : ℕ)^8327*10000000000000^6279 ≤ 4626326073629^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592041107 10000000000 4626326073629 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189181233/10000000000 : ℝ)^8327 ≤ (2196827408237/10000000000000 : ℝ)^6279 := by
    have hnat : (3189181233 : ℕ)^8327*10000000000000^6279 ≤ 2196827408237^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189181233 10000000000 2196827408237 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211906537/10000000000 : ℝ), (5592041107/10000000000 : ℝ), (3189181233/10000000000 : ℝ)] ![(15884232578871/50000000000000 : ℝ), (4626326073629/10000000000000 : ℝ), (2196827408237/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211906537/10000000000 : ℝ)|^8327 ≤ (15884232578871/50000000000000 : ℝ)^6279
        have hw : |(4211906537/10000000000 : ℝ)|=(4211906537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5592041107/10000000000 : ℝ)|^8327 ≤ (4626326073629/10000000000000 : ℝ)^6279
        have hw : |(5592041107/10000000000 : ℝ)|=(5592041107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189181233/10000000000 : ℝ)|^8327 ≤ (2196827408237/10000000000000 : ℝ)^6279
        have hw : |(3189181233/10000000000 : ℝ)|=(3189181233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13923/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4163/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4163 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4163*1^1024 ≤ 0^1024*1^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4163/1024 : ℝ) ≤ (482206289398166381/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4163 ≤ (482206289398166381/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4163*20000000000000000000^1024 ≤ 482206289398166381^1024*5^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 482206289398166381 20000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (482206289398166381/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4163 := by
      have hnat : (1 : ℕ)^1024*1^4163 ≤ 1^4163*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20482206289398166381/20000000000000000000 : ℝ) ≤ (10058774091983993/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (20482206289398166381/20000000000000000000 : ℝ)^1024 ≤ (10058774091983993/10000000000000000 : ℝ)^4163 := by
      have hnat : (20482206289398166381 : ℕ)^1024*10000000000000000^4163 ≤ 10058774091983993^4163*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20482206289398166381 20000000000000000000 10058774091983993 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058774091983993/10000000000000000 : ℝ)) (X := (20482206289398166381/20000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10482206289398166381/10000000000000000000 : ℝ) ≤ (5058774091983993/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (10482206289398166381/10000000000000000000 : ℝ)^1024 ≤ (5058774091983993/5000000000000000 : ℝ)^4163 := by
      have hnat : (10482206289398166381 : ℕ)^1024*5000000000000000^4163 ≤ 5058774091983993^4163*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10482206289398166381 10000000000000000000 5058774091983993 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058774091983993/5000000000000000 : ℝ)) (X := (10482206289398166381/10000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58774091983993/4000000000000000 : ℝ)*(0 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58774091983993/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(482206289398166381/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58774091983993/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (1 : ℝ)+(58774091983993/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058774091983993/10000000000000000 : ℝ) by norm_num, show 1+(482206289398166381/20000000000000000000 : ℝ)+(0 : ℝ)=(20482206289398166381/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(482206289398166381/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58774091983993/4000000000000000 : ℝ)*(2/5 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58774091983993/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058774091983993/5000000000000000 : ℝ) by norm_num, show 1+2*(482206289398166381/20000000000000000000 : ℝ)=(10482206289398166381/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58774091983993/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58774091983993/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58774091983993/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58774091983993/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58774091983993/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58774091983993/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-947172827/5000000000 : ℝ)*X 0 0+(3028090431/5000000000 : ℝ)*X 0 1+(4779459621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2758621649/5000000000 : ℝ)*X 1 0+(-1313631781/5000000000 : ℝ)*X 1 1+(1194865007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689655761/1250000000 : ℝ)*X 2 0+(597432361/1250000000 : ℝ)*X 2 1+(-2627261393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201639043/10000000000 : ℝ)*X 0 0+(195090723/625000000 : ℝ)*X 0 1+(1131494213/2000000000 : ℝ)*X 0 2+(4201639043/10000000000 : ℝ)*X 1 0+(195090723/625000000 : ℝ)*X 1 1+(1131494213/2000000000 : ℝ)*X 1 2+(4201639043/10000000000 : ℝ)*X 2 0+(195090723/625000000 : ℝ)*X 2 1+(1131494213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-474878611/2500000000 : ℝ)*X 0 0+(2406199687/5000000000 : ℝ)*X 0 1+(120441677/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292592523/2500000000 : ℝ)*X 1 0+(-1384638601/10000000000 : ℝ)*X 1 1+(4817667/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170370109/10000000000 : ℝ)*X 2 0+(3011041877/5000000000 : ℝ)*X 2 1+(-1384638567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211906537/10000000000 : ℝ)*X 0 0+(5592041107/10000000000 : ℝ)*X 0 1+(3189181233/10000000000 : ℝ)*X 0 2+(4211906537/10000000000 : ℝ)*X 1 0+(5592041107/10000000000 : ℝ)*X 1 1+(3189181233/10000000000 : ℝ)*X 1 2+(4211906537/10000000000 : ℝ)*X 2 0+(5592041107/10000000000 : ℝ)*X 2 1+(3189181233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13836148176178136102307/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257930337/100000000000000 : ℝ)*(base19) + (226952797/50000000000000 : ℝ)*(base23) + (1422451/625000000000 : ℝ)*(base24) + (14118187/50000000000000 : ℝ)*(base39) + (107923421/100000000000000 : ℝ)*(upper3) + (117757692393033/20000000000000 : ℝ)*(major0) + (117757692393033/20000000000000 : ℝ)*(major1) + (58878843372879/10000000000000 : ℝ)*(major2) + (391628489796259/50000000000000 : ℝ)*(sp0) + (48953574582187/6250000000000 : ℝ)*(sp1) + (783256797983949/100000000000000 : ℝ)*(sp2) + (394318757801971/100000000000000 : ℝ)*(sp3) + (471652811/100000000000000 : ℝ)*(sp4) + (165896601/25000000000000 : ℝ)*(sp7) + (3154555371107/800000000000 : ℝ)*(f.failure) + (783257479481703/100000000000000 : ℝ)*(f.sum) + (101747730227537/80000000000000000000000000000 : ℝ)*base66 + (135105774885847/40000000000000000000000000000 : ℝ)*base67 + (868732561279231/80000000000000000000000000000 : ℝ)*base70 + (102892985645847/40000000000000000000000000000 : ℝ)*base71 + (140137362787537/80000000000000000000000000000 : ℝ)*base74 + (575310301119231/80000000000000000000000000000 : ℝ)*base76 + (154725443680769/80000000000000000000000000000 : ℝ)*base77 + (45907823280769/80000000000000000000000000000 : ℝ)*base79 + (349754870879231/40000000000000000000000000000 : ℝ)*base82 + (84847/40000000000000000000 : ℝ)*base89 + (84847/40000000000000000000 : ℝ)*base91 + (484847/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21324524458179178397691/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16662681/20000000000000 : ℝ)*(base1) + (840843431/50000000000000 : ℝ)*(base19) + (841852849/50000000000000 : ℝ)*(base23) + (46178423/25000000000000 : ℝ)*(upper3) + (39216459/20000000000000 : ℝ)*(upper5) + (38838527135521/6250000000000 : ℝ)*(major0) + (38838527135521/6250000000000 : ℝ)*(major1) + (38838527135521/6250000000000 : ℝ)*(major2) + (3426689837/100000000000000 : ℝ)*(sp1) + (854060143/25000000000000 : ℝ)*(sp2) + (826661918217447/100000000000000 : ℝ)*(sp4) + (413328363263671/50000000000000 : ℝ)*(sp5) + (206664183739443/25000000000000 : ℝ)*(sp6) + (52021340332203/12500000000000 : ℝ)*(sp7) + (416170805971029/100000000000000 : ℝ)*(f.failure) + (413330917452021/50000000000000 : ℝ)*(f.sum) + (4053278465353/12500000000000000000000000000 : ℝ)*base65 + (98577375065353/25000000000000000000000000000 : ℝ)*base67 + (151615540165353/25000000000000000000000000000 : ℝ)*base69 + (165705424265353/25000000000000000000000000000 : ℝ)*base71 + (8756949184647/12500000000000000000000000000 : ℝ)*base74 + (248683115515353/25000000000000000000000000000 : ℝ)*base75 + (124457884415353/25000000000000000000000000000 : ℝ)*base77 + (176323328915353/25000000000000000000000000000 : ℝ)*base79 + (43146312815353/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14703191/5000000000000000000000 : ℝ)*base90 + (14703191/5000000000000000000000 : ℝ)*base92 + (14703191/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1134_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13923/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s1_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049792309/5000000000 : ℝ)*x 0 + (570365353/1000000000 : ℝ)*x 1 + (100011807/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049792309/5000000000 : ℝ)^8327 ≤ (12619319649311/100000000000000 : ℝ)^6279 := by
    have hnat : (1049792309 : ℕ)^8327*100000000000000^6279 ≤ 12619319649311^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049792309 5000000000 12619319649311 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570365353/1000000000 : ℝ)^8327 ≤ (11872944718393/25000000000000 : ℝ)^6279 := by
    have hnat : (570365353 : ℕ)^8327*25000000000000^6279 ≤ 11872944718393^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570365353 1000000000 11872944718393 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100011807/200000000 : ℝ)^8327 ≤ (39888901466857/100000000000000 : ℝ)^6279 := by
    have hnat : (100011807 : ℕ)^8327*100000000000000^6279 ≤ 39888901466857^6279*200000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100011807 200000000 39888901466857 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049792309/5000000000 : ℝ), (570365353/1000000000 : ℝ), (100011807/200000000 : ℝ)] ![(12619319649311/100000000000000 : ℝ), (11872944718393/25000000000000 : ℝ), (39888901466857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049792309/5000000000 : ℝ)|^8327 ≤ (12619319649311/100000000000000 : ℝ)^6279
        have hw : |(-1049792309/5000000000 : ℝ)|=(1049792309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(570365353/1000000000 : ℝ)|^8327 ≤ (11872944718393/25000000000000 : ℝ)^6279
        have hw : |(570365353/1000000000 : ℝ)|=(570365353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100011807/200000000 : ℝ)|^8327 ≤ (39888901466857/100000000000000 : ℝ)^6279
        have hw : |(100011807/200000000 : ℝ)|=(100011807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419563567/10000000000 : ℝ)*x 0 + (-2479151273/10000000000 : ℝ)*x 1 + (5000589829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419563567/10000000000 : ℝ)^8327 ≤ (22190258800891/50000000000000 : ℝ)^6279 := by
    have hnat : (5419563567 : ℕ)^8327*50000000000000^6279 ≤ 22190258800891^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419563567 10000000000 22190258800891 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2479151273/10000000000 : ℝ)^8327 ≤ (15730586422603/100000000000000 : ℝ)^6279 := by
    have hnat : (2479151273 : ℕ)^8327*100000000000000^6279 ≤ 15730586422603^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479151273 10000000000 15730586422603 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5000589829/10000000000 : ℝ)^8327 ≤ (19944447977699/50000000000000 : ℝ)^6279 := by
    have hnat : (5000589829 : ℕ)^8327*50000000000000^6279 ≤ 19944447977699^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5000589829 10000000000 19944447977699 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419563567/10000000000 : ℝ), (-2479151273/10000000000 : ℝ), (5000589829/10000000000 : ℝ)] ![(22190258800891/50000000000000 : ℝ), (15730586422603/100000000000000 : ℝ), (19944447977699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419563567/10000000000 : ℝ)|^8327 ≤ (22190258800891/50000000000000 : ℝ)^6279
        have hw : |(5419563567/10000000000 : ℝ)|=(5419563567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2479151273/10000000000 : ℝ)|^8327 ≤ (15730586422603/100000000000000 : ℝ)^6279
        have hw : |(-2479151273/10000000000 : ℝ)|=(2479151273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5000589829/10000000000 : ℝ)|^8327 ≤ (19944447977699/50000000000000 : ℝ)^6279
        have hw : |(5000589829/10000000000 : ℝ)|=(5000589829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354891341/2500000000 : ℝ)*x 0 + (2500294111/5000000000 : ℝ)*x 1 + (-99166039/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354891341/2500000000 : ℝ)^8327 ≤ (44380537117037/100000000000000 : ℝ)^6279 := by
    have hnat : (1354891341 : ℕ)^8327*100000000000000^6279 ≤ 44380537117037^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354891341 2500000000 44380537117037 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500294111/5000000000 : ℝ)^8327 ≤ (19944439477781/50000000000000 : ℝ)^6279 := by
    have hnat : (2500294111 : ℕ)^8327*50000000000000^6279 ≤ 19944439477781^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500294111 5000000000 19944439477781 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99166039/400000000 : ℝ)^8327 ≤ (3146116783003/20000000000000 : ℝ)^6279 := by
    have hnat : (99166039 : ℕ)^8327*20000000000000^6279 ≤ 3146116783003^6279*400000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99166039 400000000 3146116783003 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354891341/2500000000 : ℝ), (2500294111/5000000000 : ℝ), (-99166039/400000000 : ℝ)] ![(44380537117037/100000000000000 : ℝ), (19944439477781/50000000000000 : ℝ), (3146116783003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354891341/2500000000 : ℝ)|^8327 ≤ (44380537117037/100000000000000 : ℝ)^6279
        have hw : |(1354891341/2500000000 : ℝ)|=(1354891341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500294111/5000000000 : ℝ)|^8327 ≤ (19944439477781/50000000000000 : ℝ)^6279
        have hw : |(2500294111/5000000000 : ℝ)|=(2500294111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99166039/400000000 : ℝ)|^8327 ≤ (3146116783003/20000000000000 : ℝ)^6279
        have hw : |(-99166039/400000000 : ℝ)|=(99166039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4318115081/10000000000 : ℝ)*x 0 + (1837766347/5000000000 : ℝ)*x 1 + (2536030989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318115081/10000000000 : ℝ)^8327 ≤ (32835177657739/100000000000000 : ℝ)^6279 := by
    have hnat : (4318115081 : ℕ)^8327*100000000000000^6279 ≤ 32835177657739^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318115081 10000000000 32835177657739 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837766347/5000000000 : ℝ)^8327 ≤ (26518093207229/100000000000000 : ℝ)^6279 := by
    have hnat : (1837766347 : ℕ)^8327*100000000000000^6279 ≤ 26518093207229^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837766347 5000000000 26518093207229 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536030989/5000000000 : ℝ)^8327 ≤ (40646729115201/100000000000000 : ℝ)^6279 := by
    have hnat : (2536030989 : ℕ)^8327*100000000000000^6279 ≤ 40646729115201^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536030989 5000000000 40646729115201 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318115081/10000000000 : ℝ), (1837766347/5000000000 : ℝ), (2536030989/5000000000 : ℝ)] ![(32835177657739/100000000000000 : ℝ), (26518093207229/100000000000000 : ℝ), (40646729115201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318115081/10000000000 : ℝ)|^8327 ≤ (32835177657739/100000000000000 : ℝ)^6279
        have hw : |(4318115081/10000000000 : ℝ)|=(4318115081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837766347/5000000000 : ℝ)|^8327 ≤ (26518093207229/100000000000000 : ℝ)^6279
        have hw : |(1837766347/5000000000 : ℝ)|=(1837766347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536030989/5000000000 : ℝ)|^8327 ≤ (40646729115201/100000000000000 : ℝ)^6279
        have hw : |(2536030989/5000000000 : ℝ)|=(2536030989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100402243/10000000000 : ℝ)*x 0 + (5010219329/10000000000 : ℝ)*x 1 + (2846916543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100402243/10000000000 : ℝ)^8327 ≤ (1578229646179/12500000000000 : ℝ)^6279 := by
    have hnat : (2100402243 : ℕ)^8327*12500000000000^6279 ≤ 1578229646179^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100402243 10000000000 1578229646179 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010219329/10000000000 : ℝ)^8327 ≤ (3999079471787/10000000000000 : ℝ)^6279 := by
    have hnat : (5010219329 : ℕ)^8327*10000000000000^6279 ≤ 3999079471787^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010219329 10000000000 3999079471787 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2846916543/5000000000 : ℝ)^8327 ≤ (9476673617459/20000000000000 : ℝ)^6279 := by
    have hnat : (2846916543 : ℕ)^8327*20000000000000^6279 ≤ 9476673617459^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846916543 5000000000 9476673617459 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100402243/10000000000 : ℝ), (5010219329/10000000000 : ℝ), (2846916543/5000000000 : ℝ)] ![(1578229646179/12500000000000 : ℝ), (3999079471787/10000000000000 : ℝ), (9476673617459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100402243/10000000000 : ℝ)|^8327 ≤ (1578229646179/12500000000000 : ℝ)^6279
        have hw : |(-2100402243/10000000000 : ℝ)|=(2100402243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010219329/10000000000 : ℝ)|^8327 ≤ (3999079471787/10000000000000 : ℝ)^6279
        have hw : |(5010219329/10000000000 : ℝ)|=(5010219329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2846916543/5000000000 : ℝ)|^8327 ≤ (9476673617459/20000000000000 : ℝ)^6279
        have hw : |(2846916543/5000000000 : ℝ)|=(2846916543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047876609/2000000000 : ℝ)*x 0 + (-223238461/1250000000 : ℝ)*x 1 + (5693832801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047876609/2000000000 : ℝ)^8327 ≤ (21217231717449/50000000000000 : ℝ)^6279 := by
    have hnat : (1047876609 : ℕ)^8327*50000000000000^6279 ≤ 21217231717449^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047876609 2000000000 21217231717449 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223238461/1250000000 : ℝ)^8327 ≤ (1272771451603/12500000000000 : ℝ)^6279 := by
    have hnat : (223238461 : ℕ)^8327*12500000000000^6279 ≤ 1272771451603^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223238461 1250000000 1272771451603 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5693832801/10000000000 : ℝ)^8327 ≤ (2369168247099/5000000000000 : ℝ)^6279 := by
    have hnat : (5693832801 : ℕ)^8327*5000000000000^6279 ≤ 2369168247099^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693832801 10000000000 2369168247099 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047876609/2000000000 : ℝ), (-223238461/1250000000 : ℝ), (5693832801/10000000000 : ℝ)] ![(21217231717449/50000000000000 : ℝ), (1272771451603/12500000000000 : ℝ), (2369168247099/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047876609/2000000000 : ℝ)|^8327 ≤ (21217231717449/50000000000000 : ℝ)^6279
        have hw : |(1047876609/2000000000 : ℝ)|=(1047876609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223238461/1250000000 : ℝ)|^8327 ≤ (1272771451603/12500000000000 : ℝ)^6279
        have hw : |(-223238461/1250000000 : ℝ)|=(223238461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5693832801/10000000000 : ℝ)|^8327 ≤ (2369168247099/5000000000000 : ℝ)^6279
        have hw : |(5693832801/10000000000 : ℝ)|=(5693832801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047876619/2000000000 : ℝ)*x 0 + (5693832981/10000000000 : ℝ)*x 1 + (-1785907353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047876619/2000000000 : ℝ)^8327 ≤ (21217231985969/50000000000000 : ℝ)^6279 := by
    have hnat : (1047876619 : ℕ)^8327*50000000000000^6279 ≤ 21217231985969^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047876619 2000000000 21217231985969 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5693832981/10000000000 : ℝ)^8327 ≤ (9476673385699/20000000000000 : ℝ)^6279 := by
    have hnat : (5693832981 : ℕ)^8327*20000000000000^6279 ≤ 9476673385699^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693832981 10000000000 9476673385699 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785907353/10000000000 : ℝ)^8327 ≤ (10182169079887/100000000000000 : ℝ)^6279 := by
    have hnat : (1785907353 : ℕ)^8327*100000000000000^6279 ≤ 10182169079887^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785907353 10000000000 10182169079887 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047876619/2000000000 : ℝ), (5693832981/10000000000 : ℝ), (-1785907353/10000000000 : ℝ)] ![(21217231985969/50000000000000 : ℝ), (9476673385699/20000000000000 : ℝ), (10182169079887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047876619/2000000000 : ℝ)|^8327 ≤ (21217231985969/50000000000000 : ℝ)^6279
        have hw : |(1047876619/2000000000 : ℝ)|=(1047876619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5693832981/10000000000 : ℝ)|^8327 ≤ (9476673385699/20000000000000 : ℝ)^6279
        have hw : |(5693832981/10000000000 : ℝ)|=(5693832981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1785907353/10000000000 : ℝ)|^8327 ≤ (10182169079887/100000000000000 : ℝ)^6279
        have hw : |(-1785907353/10000000000 : ℝ)|=(1785907353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s1_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (431973581/1000000000 : ℝ)*x 0 + (505293637/1000000000 : ℝ)*x 1 + (461879797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431973581/1000000000 : ℝ)^8327 ≤ (1642576124039/5000000000000 : ℝ)^6279 := by
    have hnat : (431973581 : ℕ)^8327*5000000000000^6279 ≤ 1642576124039^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431973581 1000000000 1642576124039 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505293637/1000000000 : ℝ)^8327 ≤ (4044359306451/10000000000000 : ℝ)^6279 := by
    have hnat : (505293637 : ℕ)^8327*10000000000000^6279 ≤ 4044359306451^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505293637 1000000000 4044359306451 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461879797/1250000000 : ℝ)^8327 ≤ (26704884437283/100000000000000 : ℝ)^6279 := by
    have hnat : (461879797 : ℕ)^8327*100000000000000^6279 ≤ 26704884437283^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461879797 1250000000 26704884437283 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431973581/1000000000 : ℝ), (505293637/1000000000 : ℝ), (461879797/1250000000 : ℝ)] ![(1642576124039/5000000000000 : ℝ), (4044359306451/10000000000000 : ℝ), (26704884437283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431973581/1000000000 : ℝ)|^8327 ≤ (1642576124039/5000000000000 : ℝ)^6279
        have hw : |(431973581/1000000000 : ℝ)|=(431973581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505293637/1000000000 : ℝ)|^8327 ≤ (4044359306451/10000000000000 : ℝ)^6279
        have hw : |(505293637/1000000000 : ℝ)|=(505293637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461879797/1250000000 : ℝ)|^8327 ≤ (26704884437283/100000000000000 : ℝ)^6279
        have hw : |(461879797/1250000000 : ℝ)|=(461879797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13923/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1121/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10237/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13923/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13923/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13923/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13923/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13923/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13923/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (381/100000 : ℝ) ^ (4163/1024 : ℝ) ≤ (1829492329/12500000000000000000 : ℝ) := by
    have hpowers : (381/100000 : ℝ)^4163 ≤ (1829492329/12500000000000000000 : ℝ)^1024 := by
      have hnat : (381 : ℕ)^4163*12500000000000000000^1024 ≤ 1829492329^1024*100000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 100000 1829492329 12500000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/100000 : ℝ)) (X := (1829492329/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13923/50000 : ℝ) ^ (4163/1024 : ℝ) ≤ (138249092326518593/25000000000000000000 : ℝ) := by
    have hpowers : (13923/50000 : ℝ)^4163 ≤ (138249092326518593/25000000000000000000 : ℝ)^1024 := by
      have hnat : (13923 : ℕ)^4163*25000000000000000000^1024 ≤ 138249092326518593^1024*50000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13923 50000 138249092326518593 25000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13923/50000 : ℝ)) (X := (138249092326518593/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000001829492329/6250000000000000000 : ℝ) ≤ (500000000036001/500000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (6250000001829492329/6250000000000000000 : ℝ)^1024 ≤ (500000000036001/500000000000000 : ℝ)^4163 := by
      have hnat : (6250000001829492329 : ℕ)^1024*500000000000000^4163 ≤ 500000000036001^4163*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000001829492329 6250000000000000000 500000000036001 500000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000036001/500000000000000 : ℝ)) (X := (6250000001829492329/6250000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25138249095985503251/25000000000000000000 : ℝ) ≤ (10013574141457051/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (25138249095985503251/25000000000000000000 : ℝ)^1024 ≤ (10013574141457051/10000000000000000 : ℝ)^4163 := by
      have hnat : (25138249095985503251 : ℕ)^1024*10000000000000000^4163 ≤ 10013574141457051^4163*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25138249095985503251 25000000000000000000 10013574141457051 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013574141457051/10000000000000000 : ℝ)) (X := (25138249095985503251/25000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12638249092326518593/12500000000000000000 : ℝ) ≤ (5013574141097041/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (12638249092326518593/12500000000000000000 : ℝ)^1024 ≤ (5013574141097041/5000000000000000 : ℝ)^4163 := by
      have hnat : (12638249092326518593 : ℕ)^1024*5000000000000000^4163 ≤ 5013574141097041^4163*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12638249092326518593 12500000000000000000 5013574141097041 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013574141097041/5000000000000000 : ℝ)) (X := (12638249092326518593/12500000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1829492329/12500000000000000000 : ℝ) ≤ ((45773276087422288613/45775000000000000000 : ℝ)+2*(13574140737031/2746500000000000 : ℝ)*(381/100000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (45773276087422288613/45775000000000000000 : ℝ)+2*(13574140737031/2746500000000000 : ℝ)*(381/100000 : ℝ)=(500000000036001/500000000000000 : ℝ) by norm_num, show 1+2*(1829492329/12500000000000000000 : ℝ)=(6250000001829492329/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138249092326518593/25000000000000000000 : ℝ)+(1829492329/12500000000000000000 : ℝ) ≤ ((45773276087422288613/45775000000000000000 : ℝ)+(13574140737031/2746500000000000 : ℝ)*((13923/50000 : ℝ)+(381/100000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (45773276087422288613/45775000000000000000 : ℝ)+(13574140737031/2746500000000000 : ℝ)*((13923/50000 : ℝ)+(381/100000 : ℝ))=(10013574141457051/10000000000000000 : ℝ) by norm_num, show 1+(138249092326518593/25000000000000000000 : ℝ)+(1829492329/12500000000000000000 : ℝ)=(25138249095985503251/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138249092326518593/25000000000000000000 : ℝ) ≤ ((45773276087422288613/45775000000000000000 : ℝ)+2*(13574140737031/2746500000000000 : ℝ)*(13923/50000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (45773276087422288613/45775000000000000000 : ℝ)+2*(13574140737031/2746500000000000 : ℝ)*(13923/50000 : ℝ)=(5013574141097041/5000000000000000 : ℝ) by norm_num, show 1+2*(138249092326518593/25000000000000000000 : ℝ)=(12638249092326518593/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45773276087422288613/45775000000000000000 : ℝ)*(X 1 0+X 2 0)+(13574140737031/2746500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (381/100000 : ℝ)) (hi := (13923/50000 : ℝ)) (c := (45773276087422288613/45775000000000000000 : ℝ)) (alpha := (13574140737031/2746500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45773276087422288613/45775000000000000000 : ℝ)*(X 0 1+X 2 1)+(13574140737031/2746500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (381/100000 : ℝ)) (hi := (13923/50000 : ℝ)) (c := (45773276087422288613/45775000000000000000 : ℝ)) (alpha := (13574140737031/2746500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45773276087422288613/45775000000000000000 : ℝ)*(X 0 2+X 1 2)+(13574140737031/2746500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (381/100000 : ℝ)) (hi := (13923/50000 : ℝ)) (c := (45773276087422288613/45775000000000000000 : ℝ)) (alpha := (13574140737031/2746500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049792309/5000000000 : ℝ)*X 0 0+(570365353/1000000000 : ℝ)*X 0 1+(100011807/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5419563567/10000000000 : ℝ)*X 1 0+(-2479151273/10000000000 : ℝ)*X 1 1+(5000589829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354891341/2500000000 : ℝ)*X 2 0+(2500294111/5000000000 : ℝ)*X 2 1+(-99166039/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318115081/10000000000 : ℝ)*X 0 0+(1837766347/5000000000 : ℝ)*X 0 1+(2536030989/5000000000 : ℝ)*X 0 2+(4318115081/10000000000 : ℝ)*X 1 0+(1837766347/5000000000 : ℝ)*X 1 1+(2536030989/5000000000 : ℝ)*X 1 2+(4318115081/10000000000 : ℝ)*X 2 0+(1837766347/5000000000 : ℝ)*X 2 1+(2536030989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100402243/10000000000 : ℝ)*X 0 0+(5010219329/10000000000 : ℝ)*X 0 1+(2846916543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047876609/2000000000 : ℝ)*X 1 0+(-223238461/1250000000 : ℝ)*X 1 1+(5693832801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047876619/2000000000 : ℝ)*X 2 0+(5693832981/10000000000 : ℝ)*X 2 1+(-1785907353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431973581/1000000000 : ℝ)*X 0 0+(505293637/1000000000 : ℝ)*X 0 1+(461879797/1250000000 : ℝ)*X 0 2+(431973581/1000000000 : ℝ)*X 1 0+(505293637/1000000000 : ℝ)*X 1 1+(461879797/1250000000 : ℝ)*X 1 2+(431973581/1000000000 : ℝ)*X 2 0+(505293637/1000000000 : ℝ)*X 2 1+(461879797/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5503219766911321442769158261/2288750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282807/156250000000 : ℝ)*(base1) + (64548431/20000000000000 : ℝ)*(base19) + (165230109/25000000000000 : ℝ)*(base23) + (4867499/3125000000000 : ℝ)*(base37) + (81028873/100000000000000 : ℝ)*(lower2) + (1069203080271899/100000000000000 : ℝ)*(major0) + (1069203080271899/100000000000000 : ℝ)*(major1) + (1069203080271899/100000000000000 : ℝ)*(major2) + (711173189419601/50000000000000 : ℝ)*(sp0) + (177793228507357/12500000000000 : ℝ)*(sp1) + (284469194669931/20000000000000 : ℝ)*(sp2) + (716059109368411/100000000000000 : ℝ)*(sp3) + (436427369/100000000000000 : ℝ)*(sp4) + (483469081/100000000000000 : ℝ)*(sp5) + (358029723062429/50000000000000 : ℝ)*(f.failure) + (1422346634270091/100000000000000 : ℝ)*(f.sum) + (574816963870231/137325000000000000000000000000 : ℝ)*base66 + (13729781510680708261/13732500000000000000000000000000000 : ℝ)*base67 + (40619068660871791739/13732500000000000000000000000000000 : ℝ)*base70 + (40730698725191791739/13732500000000000000000000000000000 : ℝ)*base72 + (12043067410019/137325000000000000000000000000 : ℝ)*base73 + (161781878410879291739/13732500000000000000000000000000000 : ℝ)*base76 + (29977030969039291739/13732500000000000000000000000000000 : ℝ)*base78 + (27151035098538208261/13732500000000000000000000000000000 : ℝ)*base79 + (138997101990589/34331250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16463791/2500000000000000000000 : ℝ)*base90 + (16463791/2500000000000000000000 : ℝ)*base92 + (16463791/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21314433318872563976860242183/2288750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56274513/50000000000000 : ℝ)*(base1) + (513950239/25000000000000 : ℝ)*(base19) + (2092347347/100000000000000 : ℝ)*(base23) + (40215941/20000000000000 : ℝ)*(upper3) + (210153661/100000000000000 : ℝ)*(upper5) + (1099623586392297/100000000000000 : ℝ)*(major0) + (1099623586392297/100000000000000 : ℝ)*(major1) + (1099623586392297/100000000000000 : ℝ)*(major2) + (8343522183/100000000000000 : ℝ)*(sp1) + (1125027533/12500000000000 : ℝ)*(sp2) + (91425907089911/6250000000000 : ℝ)*(sp4) + (365701000391603/25000000000000 : ℝ)*(sp5) + (1462803308321939/100000000000000 : ℝ)*(sp6) + (368216174461403/50000000000000 : ℝ)*(sp7) + (736432461471831/100000000000000 : ℝ)*(f.failure) + (29256288017791/2000000000000 : ℝ)*(f.sum) + (5281436381231/45775000000000000000000000000 : ℝ)*base66 + (49042221666332535939/4577500000000000000000000000000000 : ℝ)*base68 + (7159229915397464061/4577500000000000000000000000000000 : ℝ)*base69 + (12307712926700035939/4577500000000000000000000000000000 : ℝ)*base72 + (114961877736903/22887500000000000000000000000 : ℝ)*base74 + (51037416824785035939/4577500000000000000000000000000000 : ℝ)*base76 + (9471272208299964061/4577500000000000000000000000000000 : ℝ)*base77 + (11867269657715035939/4577500000000000000000000000000000 : ℝ)*base80 + (10195248749297/22887500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (22828749/5000000000000000000000 : ℝ)*base90 + (22828749/5000000000000000000000 : ℝ)*base92 + (22828749/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1134_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13923/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10237/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s2_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153247979/10000000000 : ℝ)*x 0 + (689042919/1250000000 : ℝ)*x 1 + (515778501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153247979/10000000000 : ℝ)^8327 ≤ (13048831109737/100000000000000 : ℝ)^6279 := by
    have hnat : (2153247979 : ℕ)^8327*100000000000000^6279 ≤ 13048831109737^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153247979 10000000000 13048831109737 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689042919/1250000000 : ℝ)^8327 ≤ (45390899807473/100000000000000 : ℝ)^6279 := by
    have hnat : (689042919 : ℕ)^8327*100000000000000^6279 ≤ 45390899807473^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689042919 1250000000 45390899807473 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515778501/1000000000 : ℝ)^8327 ≤ (20780134533149/50000000000000 : ℝ)^6279 := by
    have hnat : (515778501 : ℕ)^8327*50000000000000^6279 ≤ 20780134533149^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515778501 1000000000 20780134533149 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153247979/10000000000 : ℝ), (689042919/1250000000 : ℝ), (515778501/1000000000 : ℝ)] ![(13048831109737/100000000000000 : ℝ), (45390899807473/100000000000000 : ℝ), (20780134533149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153247979/10000000000 : ℝ)|^8327 ≤ (13048831109737/100000000000000 : ℝ)^6279
        have hw : |(-2153247979/10000000000 : ℝ)|=(2153247979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689042919/1250000000 : ℝ)|^8327 ≤ (45390899807473/100000000000000 : ℝ)^6279
        have hw : |(689042919/1250000000 : ℝ)|=(689042919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515778501/1000000000 : ℝ)|^8327 ≤ (20780134533149/50000000000000 : ℝ)^6279
        have hw : |(515778501/1000000000 : ℝ)|=(515778501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374210819/10000000000 : ℝ)*x 0 + (-116882053/500000000 : ℝ)*x 1 + (5157786833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374210819/10000000000 : ℝ)^8327 ≤ (21944332193047/50000000000000 : ℝ)^6279 := by
    have hnat : (5374210819 : ℕ)^8327*50000000000000^6279 ≤ 21944332193047^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374210819 10000000000 21944332193047 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116882053/500000000 : ℝ)^8327 ≤ (181888088157/1250000000000 : ℝ)^6279 := by
    have hnat : (116882053 : ℕ)^8327*1250000000000^6279 ≤ 181888088157^6279*500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116882053 500000000 181888088157 1250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157786833/10000000000 : ℝ)^8327 ≤ (41560288546789/100000000000000 : ℝ)^6279 := by
    have hnat : (5157786833 : ℕ)^8327*100000000000000^6279 ≤ 41560288546789^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157786833 10000000000 41560288546789 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374210819/10000000000 : ℝ), (-116882053/500000000 : ℝ), (5157786833/10000000000 : ℝ)] ![(21944332193047/50000000000000 : ℝ), (181888088157/1250000000000 : ℝ), (41560288546789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374210819/10000000000 : ℝ)|^8327 ≤ (21944332193047/50000000000000 : ℝ)^6279
        have hw : |(5374210819/10000000000 : ℝ)|=(5374210819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116882053/500000000 : ℝ)|^8327 ≤ (181888088157/1250000000000 : ℝ)^6279
        have hw : |(-116882053/500000000 : ℝ)|=(116882053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157786833/10000000000 : ℝ)|^8327 ≤ (41560288546789/100000000000000 : ℝ)^6279
        have hw : |(5157786833/10000000000 : ℝ)|=(5157786833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374210761/10000000000 : ℝ)*x 0 + (2578893401/5000000000 : ℝ)*x 1 + (-292205147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374210761/10000000000 : ℝ)^8327 ≤ (43888663757943/100000000000000 : ℝ)^6279 := by
    have hnat : (5374210761 : ℕ)^8327*100000000000000^6279 ≤ 43888663757943^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374210761 10000000000 43888663757943 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2578893401/5000000000 : ℝ)^8327 ≤ (1662411528621/4000000000000 : ℝ)^6279 := by
    have hnat : (2578893401 : ℕ)^8327*4000000000000^6279 ≤ 1662411528621^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578893401 5000000000 1662411528621 4000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292205147/1250000000 : ℝ)^8327 ≤ (7275524005067/50000000000000 : ℝ)^6279 := by
    have hnat : (292205147 : ℕ)^8327*50000000000000^6279 ≤ 7275524005067^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292205147 1250000000 7275524005067 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374210761/10000000000 : ℝ), (2578893401/5000000000 : ℝ), (-292205147/1250000000 : ℝ)] ![(43888663757943/100000000000000 : ℝ), (1662411528621/4000000000000 : ℝ), (7275524005067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374210761/10000000000 : ℝ)|^8327 ≤ (43888663757943/100000000000000 : ℝ)^6279
        have hw : |(5374210761/10000000000 : ℝ)|=(5374210761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2578893401/5000000000 : ℝ)|^8327 ≤ (1662411528621/4000000000000 : ℝ)^6279
        have hw : |(2578893401/5000000000 : ℝ)|=(2578893401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292205147/1250000000 : ℝ)|^8327 ≤ (7275524005067/50000000000000 : ℝ)^6279
        have hw : |(-292205147/1250000000 : ℝ)|=(292205147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870981939/2000000000 : ℝ)*x 0 + (2008453883/5000000000 : ℝ)*x 1 + (188847253/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870981939/2000000000 : ℝ)^8327 ≤ (8301684516551/25000000000000 : ℝ)^6279 := by
    have hnat : (870981939 : ℕ)^8327*25000000000000^6279 ≤ 8301684516551^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870981939 2000000000 8301684516551 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008453883/5000000000 : ℝ)^8327 ≤ (7458210356003/25000000000000 : ℝ)^6279 := by
    have hnat : (2008453883 : ℕ)^8327*25000000000000^6279 ≤ 7458210356003^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008453883 5000000000 7458210356003 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188847253/400000000 : ℝ)^8327 ≤ (7392084099063/20000000000000 : ℝ)^6279 := by
    have hnat : (188847253 : ℕ)^8327*20000000000000^6279 ≤ 7392084099063^6279*400000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188847253 400000000 7392084099063 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870981939/2000000000 : ℝ), (2008453883/5000000000 : ℝ), (188847253/400000000 : ℝ)] ![(8301684516551/25000000000000 : ℝ), (7458210356003/25000000000000 : ℝ), (7392084099063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870981939/2000000000 : ℝ)|^8327 ≤ (8301684516551/25000000000000 : ℝ)^6279
        have hw : |(870981939/2000000000 : ℝ)|=(870981939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008453883/5000000000 : ℝ)|^8327 ≤ (7458210356003/25000000000000 : ℝ)^6279
        have hw : |(2008453883/5000000000 : ℝ)|=(2008453883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188847253/400000000 : ℝ)|^8327 ≤ (7392084099063/20000000000000 : ℝ)^6279
        have hw : |(188847253/400000000 : ℝ)|=(188847253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153352859/10000000000 : ℝ)*x 0 + (2580121933/5000000000 : ℝ)*x 1 + (1377464921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153352859/10000000000 : ℝ)^8327 ≤ (13049674001427/100000000000000 : ℝ)^6279 := by
    have hnat : (2153352859 : ℕ)^8327*100000000000000^6279 ≤ 13049674001427^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153352859 10000000000 13049674001427 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580121933/5000000000 : ℝ)^8327 ≤ (41586546324707/100000000000000 : ℝ)^6279 := by
    have hnat : (2580121933 : ℕ)^8327*100000000000000^6279 ≤ 41586546324707^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580121933 5000000000 41586546324707 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377464921/2500000000 : ℝ)^8327 ≤ (45363779648041/100000000000000 : ℝ)^6279 := by
    have hnat : (1377464921 : ℕ)^8327*100000000000000^6279 ≤ 45363779648041^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377464921 2500000000 45363779648041 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153352859/10000000000 : ℝ), (2580121933/5000000000 : ℝ), (1377464921/2500000000 : ℝ)] ![(13049674001427/100000000000000 : ℝ), (41586546324707/100000000000000 : ℝ), (45363779648041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153352859/10000000000 : ℝ)|^8327 ≤ (13049674001427/100000000000000 : ℝ)^6279
        have hw : |(-2153352859/10000000000 : ℝ)|=(2153352859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2580121933/5000000000 : ℝ)|^8327 ≤ (41586546324707/100000000000000 : ℝ)^6279
        have hw : |(2580121933/5000000000 : ℝ)|=(2580121933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377464921/2500000000 : ℝ)|^8327 ≤ (45363779648041/100000000000000 : ℝ)^6279
        have hw : |(1377464921/2500000000 : ℝ)|=(1377464921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642149/5000000 : ℝ)*x 0 + (-992783167/5000000000 : ℝ)*x 1 + (1377465073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642149/5000000 : ℝ)^8327 ≤ (21458779577497/50000000000000 : ℝ)^6279 := by
    have hnat : (2642149 : ℕ)^8327*50000000000000^6279 ≤ 21458779577497^6279*5000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642149 5000000 21458779577497 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992783167/5000000000 : ℝ)^8327 ≤ (5859327272271/50000000000000 : ℝ)^6279 := by
    have hnat : (992783167 : ℕ)^8327*50000000000000^6279 ≤ 5859327272271^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992783167 5000000000 5859327272271 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377465073/2500000000 : ℝ)^8327 ≤ (45363786286547/100000000000000 : ℝ)^6279 := by
    have hnat : (1377465073 : ℕ)^8327*100000000000000^6279 ≤ 45363786286547^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377465073 2500000000 45363786286547 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642149/5000000 : ℝ), (-992783167/5000000000 : ℝ), (1377465073/2500000000 : ℝ)] ![(21458779577497/50000000000000 : ℝ), (5859327272271/50000000000000 : ℝ), (45363786286547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642149/5000000 : ℝ)|^8327 ≤ (21458779577497/50000000000000 : ℝ)^6279
        have hw : |(2642149/5000000 : ℝ)|=(2642149/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992783167/5000000000 : ℝ)|^8327 ≤ (5859327272271/50000000000000 : ℝ)^6279
        have hw : |(-992783167/5000000000 : ℝ)|=(992783167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377465073/2500000000 : ℝ)|^8327 ≤ (45363786286547/100000000000000 : ℝ)^6279
        have hw : |(1377465073/2500000000 : ℝ)|=(1377465073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284296639/10000000000 : ℝ)*x 0 + (550986013/1000000000 : ℝ)*x 1 + (-1985568433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284296639/10000000000 : ℝ)^8327 ≤ (42917544496009/100000000000000 : ℝ)^6279 := by
    have hnat : (5284296639 : ℕ)^8327*100000000000000^6279 ≤ 42917544496009^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284296639 10000000000 42917544496009 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550986013/1000000000 : ℝ)^8327 ≤ (9072756903547/20000000000000 : ℝ)^6279 := by
    have hnat : (550986013 : ℕ)^8327*20000000000000^6279 ≤ 9072756903547^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550986013 1000000000 9072756903547 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985568433/10000000000 : ℝ)^8327 ≤ (1171867097327/10000000000000 : ℝ)^6279 := by
    have hnat : (1985568433 : ℕ)^8327*10000000000000^6279 ≤ 1171867097327^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985568433 10000000000 1171867097327 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284296639/10000000000 : ℝ), (550986013/1000000000 : ℝ), (-1985568433/10000000000 : ℝ)] ![(42917544496009/100000000000000 : ℝ), (9072756903547/20000000000000 : ℝ), (1171867097327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284296639/10000000000 : ℝ)|^8327 ≤ (42917544496009/100000000000000 : ℝ)^6279
        have hw : |(5284296639/10000000000 : ℝ)|=(5284296639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550986013/1000000000 : ℝ)|^8327 ≤ (9072756903547/20000000000000 : ℝ)^6279
        have hw : |(550986013/1000000000 : ℝ)|=(550986013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985568433/10000000000 : ℝ)|^8327 ≤ (1171867097327/10000000000000 : ℝ)^6279
        have hw : |(-1985568433/10000000000 : ℝ)|=(1985568433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s2_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435511737/1000000000 : ℝ)*x 0 + (4716298693/10000000000 : ℝ)*x 1 + (402183949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435511737/1000000000 : ℝ)^8327 ≤ (4151104766403/12500000000000 : ℝ)^6279 := by
    have hnat : (435511737 : ℕ)^8327*12500000000000^6279 ≤ 4151104766403^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435511737 1000000000 4151104766403 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4716298693/10000000000 : ℝ)^8327 ≤ (7381947435747/20000000000000 : ℝ)^6279 := by
    have hnat : (4716298693 : ℕ)^8327*20000000000000^6279 ≤ 7381947435747^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4716298693 10000000000 7381947435747 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402183949/1000000000 : ℝ)^8327 ≤ (29881424670081/100000000000000 : ℝ)^6279 := by
    have hnat : (402183949 : ℕ)^8327*100000000000000^6279 ≤ 29881424670081^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402183949 1000000000 29881424670081 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435511737/1000000000 : ℝ), (4716298693/10000000000 : ℝ), (402183949/1000000000 : ℝ)] ![(4151104766403/12500000000000 : ℝ), (7381947435747/20000000000000 : ℝ), (29881424670081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435511737/1000000000 : ℝ)|^8327 ≤ (4151104766403/12500000000000 : ℝ)^6279
        have hw : |(435511737/1000000000 : ℝ)|=(435511737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4716298693/10000000000 : ℝ)|^8327 ≤ (7381947435747/20000000000000 : ℝ)^6279
        have hw : |(4716298693/10000000000 : ℝ)|=(4716298693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402183949/1000000000 : ℝ)|^8327 ≤ (29881424670081/100000000000000 : ℝ)^6279
        have hw : |(402183949/1000000000 : ℝ)|=(402183949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10237/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4517/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16527/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10237/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10237/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1121/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10237/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10237/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1121/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10237/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10237/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1121/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1121/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (408688263219083/50000000000000000000 : ℝ) := by
    have hpowers : (1121/20000 : ℝ)^4163 ≤ (408688263219083/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1121 : ℕ)^4163*50000000000000000000^1024 ≤ 408688263219083^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 20000 408688263219083 50000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/20000 : ℝ)) (X := (408688263219083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10237/50000 : ℝ) ^ (4163/1024 : ℝ) ≤ (158395559988189277/100000000000000000000 : ℝ) := by
    have hpowers : (10237/50000 : ℝ)^4163 ≤ (158395559988189277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10237 : ℕ)^4163*100000000000000000000^1024 ≤ 158395559988189277^1024*50000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10237 50000 158395559988189277 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10237/50000 : ℝ)) (X := (158395559988189277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000408688263219083/25000000000000000000 : ℝ) ≤ (10000040210828949/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (25000408688263219083/25000000000000000000 : ℝ)^1024 ≤ (10000040210828949/10000000000000000 : ℝ)^4163 := by
      have hnat : (25000408688263219083 : ℕ)^1024*10000000000000000^4163 ≤ 10000040210828949^4163*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000408688263219083 25000000000000000000 10000040210828949 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000040210828949/10000000000000000 : ℝ)) (X := (25000408688263219083/25000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100159212936514627443/100000000000000000000 : ℝ) ≤ (10003913914882423/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (100159212936514627443/100000000000000000000 : ℝ)^1024 ≤ (10003913914882423/10000000000000000 : ℝ)^4163 := by
      have hnat : (100159212936514627443 : ℕ)^1024*10000000000000000^4163 ≤ 10003913914882423^4163*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100159212936514627443 100000000000000000000 10003913914882423 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003913914882423/10000000000000000 : ℝ)) (X := (100159212936514627443/100000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50158395559988189277/50000000000000000000 : ℝ) ≤ (10007787618935897/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50158395559988189277/50000000000000000000 : ℝ)^1024 ≤ (10007787618935897/10000000000000000 : ℝ)^4163 := by
      have hnat : (50158395559988189277 : ℕ)^1024*10000000000000000^4163 ≤ 10007787618935897^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50158395559988189277 50000000000000000000 10007787618935897 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007787618935897/10000000000000000 : ℝ)) (X := (50158395559988189277/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(408688263219083/50000000000000000000 : ℝ) ≤ ((148647173672376199141/148690000000000000000 : ℝ)+2*(1936852026737/743450000000000 : ℝ)*(1121/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (148647173672376199141/148690000000000000000 : ℝ)+2*(1936852026737/743450000000000 : ℝ)*(1121/20000 : ℝ)=(10000040210828949/10000000000000000 : ℝ) by norm_num, show 1+2*(408688263219083/50000000000000000000 : ℝ)=(25000408688263219083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(158395559988189277/100000000000000000000 : ℝ)+(408688263219083/50000000000000000000 : ℝ) ≤ ((148647173672376199141/148690000000000000000 : ℝ)+(1936852026737/743450000000000 : ℝ)*((10237/50000 : ℝ)+(1121/20000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (148647173672376199141/148690000000000000000 : ℝ)+(1936852026737/743450000000000 : ℝ)*((10237/50000 : ℝ)+(1121/20000 : ℝ))=(10003913914882423/10000000000000000 : ℝ) by norm_num, show 1+(158395559988189277/100000000000000000000 : ℝ)+(408688263219083/50000000000000000000 : ℝ)=(100159212936514627443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(158395559988189277/100000000000000000000 : ℝ) ≤ ((148647173672376199141/148690000000000000000 : ℝ)+2*(1936852026737/743450000000000 : ℝ)*(10237/50000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (148647173672376199141/148690000000000000000 : ℝ)+2*(1936852026737/743450000000000 : ℝ)*(10237/50000 : ℝ)=(10007787618935897/10000000000000000 : ℝ) by norm_num, show 1+2*(158395559988189277/100000000000000000000 : ℝ)=(50158395559988189277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (148647173672376199141/148690000000000000000 : ℝ)*(X 1 0+X 2 0)+(1936852026737/743450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (1121/20000 : ℝ)) (hi := (10237/50000 : ℝ)) (c := (148647173672376199141/148690000000000000000 : ℝ)) (alpha := (1936852026737/743450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (148647173672376199141/148690000000000000000 : ℝ)*(X 0 1+X 2 1)+(1936852026737/743450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (1121/20000 : ℝ)) (hi := (10237/50000 : ℝ)) (c := (148647173672376199141/148690000000000000000 : ℝ)) (alpha := (1936852026737/743450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (148647173672376199141/148690000000000000000 : ℝ)*(X 0 2+X 1 2)+(1936852026737/743450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (1121/20000 : ℝ)) (hi := (10237/50000 : ℝ)) (c := (148647173672376199141/148690000000000000000 : ℝ)) (alpha := (1936852026737/743450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2153247979/10000000000 : ℝ)*X 0 0+(689042919/1250000000 : ℝ)*X 0 1+(515778501/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374210819/10000000000 : ℝ)*X 1 0+(-116882053/500000000 : ℝ)*X 1 1+(5157786833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374210761/10000000000 : ℝ)*X 2 0+(2578893401/5000000000 : ℝ)*X 2 1+(-292205147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870981939/2000000000 : ℝ)*X 0 0+(2008453883/5000000000 : ℝ)*X 0 1+(188847253/400000000 : ℝ)*X 0 2+(870981939/2000000000 : ℝ)*X 1 0+(2008453883/5000000000 : ℝ)*X 1 1+(188847253/400000000 : ℝ)*X 1 2+(870981939/2000000000 : ℝ)*X 2 0+(2008453883/5000000000 : ℝ)*X 2 1+(188847253/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153352859/10000000000 : ℝ)*X 0 0+(2580121933/5000000000 : ℝ)*X 0 1+(1377464921/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642149/5000000 : ℝ)*X 1 0+(-992783167/5000000000 : ℝ)*X 1 1+(1377465073/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284296639/10000000000 : ℝ)*X 2 0+(550986013/1000000000 : ℝ)*X 2 1+(-1985568433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435511737/1000000000 : ℝ)*X 0 0+(4716298693/10000000000 : ℝ)*X 0 1+(402183949/1000000000 : ℝ)*X 0 2+(435511737/1000000000 : ℝ)*X 1 0+(4716298693/10000000000 : ℝ)*X 1 1+(402183949/1000000000 : ℝ)*X 1 2+(435511737/1000000000 : ℝ)*X 2 0+(4716298693/10000000000 : ℝ)*X 2 1+(402183949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21956526271699548989271570477/3717250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241382073/100000000000000 : ℝ)*(base19) + (43009253/50000000000000 : ℝ)*(base23) + (62669483/100000000000000 : ℝ)*(upper2) + (17511703/10000000000000 : ℝ)*(upper3) + (25961319/20000000000000 : ℝ)*(upper4) + (1060086759677567/50000000000000 : ℝ)*(major0) + (1060086759677567/50000000000000 : ℝ)*(major1) + (1060086759677567/50000000000000 : ℝ)*(major2) + (352553205088633/12500000000000 : ℝ)*(sp0) + (564087669834539/20000000000000 : ℝ)*(sp1) + (1410219252268131/50000000000000 : ℝ)*(sp2) + (1419904749248119/100000000000000 : ℝ)*(sp3) + (1618730713/12500000000000 : ℝ)*(sp4) + (875504689/25000000000000 : ℝ)*(sp7) + (354977062816719/25000000000000 : ℝ)*(f.failure) + (176277411909673/6250000000000 : ℝ)*(f.sum) + (149052014837869/74345000000000000000000000000 : ℝ)*base66 + (113513686147555169947/7434500000000000000000000000000000 : ℝ)*base67 + (34603099946478669947/7434500000000000000000000000000000 : ℝ)*base69 + (93259726312183169947/7434500000000000000000000000000000 : ℝ)*base71 + (89751710638813/37172500000000000000000000000 : ℝ)*base73 + (48330184841693169947/7434500000000000000000000000000000 : ℝ)*base75 + (23474095680276669947/7434500000000000000000000000000000 : ℝ)*base77 + (113104640463101169947/7434500000000000000000000000000000 : ℝ)*base79 + (91337192052481/74345000000000000000000000000 : ℝ)*base81 + (4628299/1250000000000000000000 : ℝ)*base89 + (4628299/1250000000000000000000 : ℝ)*base91 + (4628299/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8378475878996909561813208459/743450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516545667/25000000000000 : ℝ)*(base19) + (1517652969/100000000000000 : ℝ)*(base23) + (12568049/5000000000000 : ℝ)*(upper2) + (36439073/25000000000000 : ℝ)*(upper3) + (158707881/50000000000000 : ℝ)*(upper5) + (430024440065467/20000000000000 : ℝ)*(major0) + (430024440065467/20000000000000 : ℝ)*(major1) + (430024440065467/20000000000000 : ℝ)*(major2) + (1696900027/6250000000000 : ℝ)*(sp1) + (10252028689/100000000000000 : ℝ)*(sp2) + (1430139372963177/50000000000000 : ℝ)*(sp4) + (1430124764671627/50000000000000 : ℝ)*(sp5) + (357533372030587/12500000000000 : ℝ)*(sp6) + (287993055814173/20000000000000 : ℝ)*(sp7) + (287993055814173/20000000000000 : ℝ)*(f.failure) + (1430139372963177/50000000000000 : ℝ)*(f.sum) + (45796711166679/7434500000000000000000000000 : ℝ)*base66 + (22923143198940763847/2973800000000000000000000000000000 : ℝ)*base67 + (15467686898738163847/2973800000000000000000000000000000 : ℝ)*base69 + (13979538283384563847/2973800000000000000000000000000000 : ℝ)*base71 + (17493713967617/14869000000000000000000000000 : ℝ)*base73 + (1667556534196236153/2973800000000000000000000000000000 : ℝ)*base76 + (7566439659927563847/2973800000000000000000000000000000 : ℝ)*base77 + (14752067155483563847/2973800000000000000000000000000000 : ℝ)*base79 + (4864296822479/3717250000000000000000000000 : ℝ)*base81 + (1270033/1000000000000000000000 : ℝ)*base89 + (1270033/1000000000000000000000 : ℝ)*base91 + (1270033/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1134_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10237/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1134_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1134_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1134_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1134_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
