-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1092_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:15.034591+00:00
-- url     : https://prove2.me/submissions/d1c6fded-8ed7-4f1c-9422-dae94ee21989

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
theorem support_rectangle_w1092_s3_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186630509/10000000000 : ℝ)*x 0 + (2717280679/5000000000 : ℝ)*x 1 + (5227137917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186630509/10000000000 : ℝ)^8285 ≤ (6636698396921/50000000000000 : ℝ)^6237 := by
    have hnat : (2186630509 : ℕ)^8285*50000000000000^6237 ≤ 6636698396921^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186630509 10000000000 6636698396921 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717280679/5000000000 : ℝ)^8285 ≤ (22241922422683/50000000000000 : ℝ)^6237 := by
    have hnat : (2717280679 : ℕ)^8285*50000000000000^6237 ≤ 22241922422683^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717280679 5000000000 22241922422683 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227137917/10000000000 : ℝ)^8285 ≤ (10560689586733/25000000000000 : ℝ)^6237 := by
    have hnat : (5227137917 : ℕ)^8285*25000000000000^6237 ≤ 10560689586733^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227137917 10000000000 10560689586733 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186630509/10000000000 : ℝ), (2717280679/5000000000 : ℝ), (5227137917/10000000000 : ℝ)] ![(6636698396921/50000000000000 : ℝ), (22241922422683/50000000000000 : ℝ), (10560689586733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186630509/10000000000 : ℝ)|^8285 ≤ (6636698396921/50000000000000 : ℝ)^6237
        have hw : |(-2186630509/10000000000 : ℝ)|=(2186630509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717280679/5000000000 : ℝ)|^8285 ≤ (22241922422683/50000000000000 : ℝ)^6237
        have hw : |(2717280679/5000000000 : ℝ)|=(2717280679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227137917/10000000000 : ℝ)|^8285 ≤ (10560689586733/25000000000000 : ℝ)^6237
        have hw : |(5227137917/10000000000 : ℝ)|=(5227137917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338757133/2500000000 : ℝ)*x 0 + (-2292780229/10000000000 : ℝ)*x 1 + (326696113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338757133/2500000000 : ℝ)^8285 ≤ (8724231747383/20000000000000 : ℝ)^6237 := by
    have hnat : (1338757133 : ℕ)^8285*20000000000000^6237 ≤ 8724231747383^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338757133 2500000000 8724231747383 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292780229/10000000000 : ℝ)^8285 ≤ (14136084066513/100000000000000 : ℝ)^6237 := by
    have hnat : (2292780229 : ℕ)^8285*100000000000000^6237 ≤ 14136084066513^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292780229 10000000000 14136084066513 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326696113/625000000 : ℝ)^8285 ≤ (5280344647101/12500000000000 : ℝ)^6237 := by
    have hnat : (326696113 : ℕ)^8285*12500000000000^6237 ≤ 5280344647101^6237*625000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326696113 625000000 5280344647101 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338757133/2500000000 : ℝ), (-2292780229/10000000000 : ℝ), (326696113/625000000 : ℝ)] ![(8724231747383/20000000000000 : ℝ), (14136084066513/100000000000000 : ℝ), (5280344647101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338757133/2500000000 : ℝ)|^8285 ≤ (8724231747383/20000000000000 : ℝ)^6237
        have hw : |(1338757133/2500000000 : ℝ)|=(1338757133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2292780229/10000000000 : ℝ)|^8285 ≤ (14136084066513/100000000000000 : ℝ)^6237
        have hw : |(-2292780229/10000000000 : ℝ)|=(2292780229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326696113/625000000 : ℝ)|^8285 ≤ (5280344647101/12500000000000 : ℝ)^6237
        have hw : |(326696113/625000000 : ℝ)|=(326696113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677514207/5000000000 : ℝ)*x 0 + (20908553/40000000 : ℝ)*x 1 + (-1146389903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677514207/5000000000 : ℝ)^8285 ≤ (21810578730041/50000000000000 : ℝ)^6237 := by
    have hnat : (2677514207 : ℕ)^8285*50000000000000^6237 ≤ 21810578730041^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677514207 5000000000 21810578730041 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20908553/40000000 : ℝ)^8285 ≤ (2640172620107/6250000000000 : ℝ)^6237 := by
    have hnat : (20908553 : ℕ)^8285*6250000000000^6237 ≤ 2640172620107^6237*40000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20908553 40000000 2640172620107 6250000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146389903/5000000000 : ℝ)^8285 ≤ (7068040301073/50000000000000 : ℝ)^6237 := by
    have hnat : (1146389903 : ℕ)^8285*50000000000000^6237 ≤ 7068040301073^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146389903 5000000000 7068040301073 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677514207/5000000000 : ℝ), (20908553/40000000 : ℝ), (-1146389903/5000000000 : ℝ)] ![(21810578730041/50000000000000 : ℝ), (2640172620107/6250000000000 : ℝ), (7068040301073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677514207/5000000000 : ℝ)|^8285 ≤ (21810578730041/50000000000000 : ℝ)^6237
        have hw : |(2677514207/5000000000 : ℝ)|=(2677514207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20908553/40000000 : ℝ)|^8285 ≤ (2640172620107/6250000000000 : ℝ)^6237
        have hw : |(20908553/40000000 : ℝ)|=(20908553/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1146389903/5000000000 : ℝ)|^8285 ≤ (7068040301073/50000000000000 : ℝ)^6237
        have hw : |(-1146389903/5000000000 : ℝ)|=(1146389903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184581379/5000000000 : ℝ)*x 0 + (2084827613/5000000000 : ℝ)*x 1 + (4578274767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184581379/5000000000 : ℝ)^8285 ≤ (16645172911889/50000000000000 : ℝ)^6237 := by
    have hnat : (2184581379 : ℕ)^8285*50000000000000^6237 ≤ 16645172911889^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184581379 5000000000 16645172911889 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084827613/5000000000 : ℝ)^8285 ≤ (15643181949569/50000000000000 : ℝ)^6237 := by
    have hnat : (2084827613 : ℕ)^8285*50000000000000^6237 ≤ 15643181949569^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084827613 5000000000 15643181949569 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578274767/10000000000 : ℝ)^8285 ≤ (7084658053703/20000000000000 : ℝ)^6237 := by
    have hnat : (4578274767 : ℕ)^8285*20000000000000^6237 ≤ 7084658053703^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578274767 10000000000 7084658053703 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184581379/5000000000 : ℝ), (2084827613/5000000000 : ℝ), (4578274767/10000000000 : ℝ)] ![(16645172911889/50000000000000 : ℝ), (15643181949569/50000000000000 : ℝ), (7084658053703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184581379/5000000000 : ℝ)|^8285 ≤ (16645172911889/50000000000000 : ℝ)^6237
        have hw : |(2184581379/5000000000 : ℝ)|=(2184581379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084827613/5000000000 : ℝ)|^8285 ≤ (15643181949569/50000000000000 : ℝ)^6237
        have hw : |(2084827613/5000000000 : ℝ)|=(2084827613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578274767/10000000000 : ℝ)|^8285 ≤ (7084658053703/20000000000000 : ℝ)^6237
        have hw : |(4578274767/10000000000 : ℝ)|=(4578274767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186651369/10000000000 : ℝ)*x 0 + (261398609/500000000 : ℝ)*x 1 + (217348887/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186651369/10000000000 : ℝ)^8285 ≤ (13273564998659/100000000000000 : ℝ)^6237 := by
    have hnat : (2186651369 : ℕ)^8285*100000000000000^6237 ≤ 13273564998659^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186651369 10000000000 13273564998659 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261398609/500000000 : ℝ)^8285 ≤ (42251714457383/100000000000000 : ℝ)^6237 := by
    have hnat : (261398609 : ℕ)^8285*100000000000000^6237 ≤ 42251714457383^6237*500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261398609 500000000 42251714457383 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217348887/400000000 : ℝ)^8285 ≤ (44474720530659/100000000000000 : ℝ)^6237 := by
    have hnat : (217348887 : ℕ)^8285*100000000000000^6237 ≤ 44474720530659^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217348887 400000000 44474720530659 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186651369/10000000000 : ℝ), (261398609/500000000 : ℝ), (217348887/400000000 : ℝ)] ![(13273564998659/100000000000000 : ℝ), (42251714457383/100000000000000 : ℝ), (44474720530659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186651369/10000000000 : ℝ)|^8285 ≤ (13273564998659/100000000000000 : ℝ)^6237
        have hw : |(-2186651369/10000000000 : ℝ)|=(2186651369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261398609/500000000 : ℝ)|^8285 ≤ (42251714457383/100000000000000 : ℝ)^6237
        have hw : |(261398609/500000000 : ℝ)|=(261398609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217348887/400000000 : ℝ)|^8285 ≤ (44474720530659/100000000000000 : ℝ)^6237
        have hw : |(217348887/400000000 : ℝ)|=(217348887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325668557/2500000000 : ℝ)*x 0 + (-2086195733/10000000000 : ℝ)*x 1 + (5433722451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325668557/2500000000 : ℝ)^8285 ≤ (2690972749413/6250000000000 : ℝ)^6237 := by
    have hnat : (1325668557 : ℕ)^8285*6250000000000^6237 ≤ 2690972749413^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325668557 2500000000 2690972749413 6250000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086195733/10000000000 : ℝ)^8285 ≤ (6234856232839/50000000000000 : ℝ)^6237 := by
    have hnat : (2086195733 : ℕ)^8285*50000000000000^6237 ≤ 6234856232839^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086195733 10000000000 6234856232839 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433722451/10000000000 : ℝ)^8285 ≤ (4447472353149/10000000000000 : ℝ)^6237 := by
    have hnat : (5433722451 : ℕ)^8285*10000000000000^6237 ≤ 4447472353149^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433722451 10000000000 4447472353149 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325668557/2500000000 : ℝ), (-2086195733/10000000000 : ℝ), (5433722451/10000000000 : ℝ)] ![(2690972749413/6250000000000 : ℝ), (6234856232839/50000000000000 : ℝ), (4447472353149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325668557/2500000000 : ℝ)|^8285 ≤ (2690972749413/6250000000000 : ℝ)^6237
        have hw : |(1325668557/2500000000 : ℝ)|=(1325668557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086195733/10000000000 : ℝ)|^8285 ≤ (6234856232839/50000000000000 : ℝ)^6237
        have hw : |(-2086195733/10000000000 : ℝ)|=(2086195733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433722451/10000000000 : ℝ)|^8285 ≤ (4447472353149/10000000000000 : ℝ)^6237
        have hw : |(5433722451/10000000000 : ℝ)|=(5433722451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302674367/10000000000 : ℝ)*x 0 + (5433722199/10000000000 : ℝ)*x 1 + (-2086195889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302674367/10000000000 : ℝ)^8285 ≤ (4305556548983/10000000000000 : ℝ)^6237 := by
    have hnat : (5302674367 : ℕ)^8285*10000000000000^6237 ≤ 4305556548983^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302674367 10000000000 4305556548983 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433722199/10000000000 : ℝ)^8285 ≤ (44474720791601/100000000000000 : ℝ)^6237 := by
    have hnat : (5433722199 : ℕ)^8285*100000000000000^6237 ≤ 44474720791601^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433722199 10000000000 44474720791601 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086195889/10000000000 : ℝ)^8285 ≤ (1558714213039/12500000000000 : ℝ)^6237 := by
    have hnat : (2086195889 : ℕ)^8285*12500000000000^6237 ≤ 1558714213039^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086195889 10000000000 1558714213039 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302674367/10000000000 : ℝ), (5433722199/10000000000 : ℝ), (-2086195889/10000000000 : ℝ)] ![(4305556548983/10000000000000 : ℝ), (44474720791601/100000000000000 : ℝ), (1558714213039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302674367/10000000000 : ℝ)|^8285 ≤ (4305556548983/10000000000000 : ℝ)^6237
        have hw : |(5302674367/10000000000 : ℝ)|=(5302674367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433722199/10000000000 : ℝ)|^8285 ≤ (44474720791601/100000000000000 : ℝ)^6237
        have hw : |(5433722199/10000000000 : ℝ)|=(5433722199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086195889/10000000000 : ℝ)|^8285 ≤ (1558714213039/12500000000000 : ℝ)^6237
        have hw : |(-2086195889/10000000000 : ℝ)|=(2086195889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s3_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369203411/10000000000 : ℝ)*x 0 + (4576632111/10000000000 : ℝ)*x 1 + (4171307601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369203411/10000000000 : ℝ)^8285 ≤ (33290757286141/100000000000000 : ℝ)^6237 := by
    have hnat : (4369203411 : ℕ)^8285*100000000000000^6237 ≤ 33290757286141^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369203411 10000000000 33290757286141 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4576632111/10000000000 : ℝ)^8285 ≤ (3540640823137/10000000000000 : ℝ)^6237 := by
    have hnat : (4576632111 : ℕ)^8285*10000000000000^6237 ≤ 3540640823137^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576632111 10000000000 3540640823137 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171307601/10000000000 : ℝ)^8285 ≤ (15651417233703/50000000000000 : ℝ)^6237 := by
    have hnat : (4171307601 : ℕ)^8285*50000000000000^6237 ≤ 15651417233703^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171307601 10000000000 15651417233703 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369203411/10000000000 : ℝ), (4576632111/10000000000 : ℝ), (4171307601/10000000000 : ℝ)] ![(33290757286141/100000000000000 : ℝ), (3540640823137/10000000000000 : ℝ), (15651417233703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369203411/10000000000 : ℝ)|^8285 ≤ (33290757286141/100000000000000 : ℝ)^6237
        have hw : |(4369203411/10000000000 : ℝ)|=(4369203411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4576632111/10000000000 : ℝ)|^8285 ≤ (3540640823137/10000000000000 : ℝ)^6237
        have hw : |(4576632111/10000000000 : ℝ)|=(4576632111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171307601/10000000000 : ℝ)|^8285 ≤ (15651417233703/50000000000000 : ℝ)^6237
        have hw : |(4171307601/10000000000 : ℝ)|=(4171307601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14869/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4419/50000 : ℝ) ^ (2071/512 : ℝ) ≤ (2735610356436599/50000000000000000000 : ℝ) := by
    have hpowers : (4419/50000 : ℝ)^2071 ≤ (2735610356436599/50000000000000000000 : ℝ)^512 := by
      have hnat : (4419 : ℕ)^2071*50000000000000000000^512 ≤ 2735610356436599^512*50000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4419 50000 2735610356436599 50000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4419/50000 : ℝ)) (X := (2735610356436599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16657/100000 : ℝ) ^ (2071/512 : ℝ) ≤ (35513200672247597/50000000000000000000 : ℝ) := by
    have hpowers : (16657/100000 : ℝ)^2071 ≤ (35513200672247597/50000000000000000000 : ℝ)^512 := by
      have hnat : (16657 : ℕ)^2071*50000000000000000000^512 ≤ 35513200672247597^512*100000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16657 100000 35513200672247597 50000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16657/100000 : ℝ)) (X := (35513200672247597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002735610356436599/25000000000000000000 : ℝ) ≤ (10000270511795201/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25002735610356436599/25000000000000000000 : ℝ)^512 ≤ (10000270511795201/10000000000000000 : ℝ)^2071 := by
      have hnat : (25002735610356436599 : ℕ)^512*10000000000000000^2071 ≤ 10000270511795201^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002735610356436599 25000000000000000000 10000270511795201 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270511795201/10000000000000000 : ℝ)) (X := (25002735610356436599/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12509562202757171049/12500000000000000000 : ℝ) ≤ (5000945328592859/5000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (12509562202757171049/12500000000000000000 : ℝ)^512 ≤ (5000945328592859/5000000000000000 : ℝ)^2071 := by
      have hnat : (12509562202757171049 : ℕ)^512*5000000000000000^2071 ≤ 5000945328592859^2071*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509562202757171049 12500000000000000000 5000945328592859 5000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000945328592859/5000000000000000 : ℝ)) (X := (12509562202757171049/12500000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25035513200672247597/25000000000000000000 : ℝ) ≤ (2000702160515247/2000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25035513200672247597/25000000000000000000 : ℝ)^512 ≤ (2000702160515247/2000000000000000 : ℝ)^2071 := by
      have hnat : (25035513200672247597 : ℕ)^512*2000000000000000^2071 ≤ 2000702160515247^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035513200672247597 25000000000000000000 2000702160515247 2000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000702160515247/2000000000000000 : ℝ)) (X := (25035513200672247597/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2735610356436599/50000000000000000000 : ℝ) ≤ ((78163477441803898127/78190000000000000000 : ℝ)+2*(1620145390517/781900000000000 : ℝ)*(4419/50000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (78163477441803898127/78190000000000000000 : ℝ)+2*(1620145390517/781900000000000 : ℝ)*(4419/50000 : ℝ)=(10000270511795201/10000000000000000 : ℝ) by norm_num, show 1+2*(2735610356436599/50000000000000000000 : ℝ)=(25002735610356436599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35513200672247597/50000000000000000000 : ℝ)+(2735610356436599/50000000000000000000 : ℝ) ≤ ((78163477441803898127/78190000000000000000 : ℝ)+(1620145390517/781900000000000 : ℝ)*((16657/100000 : ℝ)+(4419/50000 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (78163477441803898127/78190000000000000000 : ℝ)+(1620145390517/781900000000000 : ℝ)*((16657/100000 : ℝ)+(4419/50000 : ℝ))=(5000945328592859/5000000000000000 : ℝ) by norm_num, show 1+(35513200672247597/50000000000000000000 : ℝ)+(2735610356436599/50000000000000000000 : ℝ)=(12509562202757171049/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35513200672247597/50000000000000000000 : ℝ) ≤ ((78163477441803898127/78190000000000000000 : ℝ)+2*(1620145390517/781900000000000 : ℝ)*(16657/100000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (78163477441803898127/78190000000000000000 : ℝ)+2*(1620145390517/781900000000000 : ℝ)*(16657/100000 : ℝ)=(2000702160515247/2000000000000000 : ℝ) by norm_num, show 1+2*(35513200672247597/50000000000000000000 : ℝ)=(25035513200672247597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78163477441803898127/78190000000000000000 : ℝ)*(X 1 0+X 2 0)+(1620145390517/781900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (16657/100000 : ℝ)) (c := (78163477441803898127/78190000000000000000 : ℝ)) (alpha := (1620145390517/781900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78163477441803898127/78190000000000000000 : ℝ)*(X 0 1+X 2 1)+(1620145390517/781900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (16657/100000 : ℝ)) (c := (78163477441803898127/78190000000000000000 : ℝ)) (alpha := (1620145390517/781900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78163477441803898127/78190000000000000000 : ℝ)*(X 0 2+X 1 2)+(1620145390517/781900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (4419/50000 : ℝ)) (hi := (16657/100000 : ℝ)) (c := (78163477441803898127/78190000000000000000 : ℝ)) (alpha := (1620145390517/781900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2186630509/10000000000 : ℝ)*X 0 0+(2717280679/5000000000 : ℝ)*X 0 1+(5227137917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338757133/2500000000 : ℝ)*X 1 0+(-2292780229/10000000000 : ℝ)*X 1 1+(326696113/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677514207/5000000000 : ℝ)*X 2 0+(20908553/40000000 : ℝ)*X 2 1+(-1146389903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184581379/5000000000 : ℝ)*X 0 0+(2084827613/5000000000 : ℝ)*X 0 1+(4578274767/10000000000 : ℝ)*X 0 2+(2184581379/5000000000 : ℝ)*X 1 0+(2084827613/5000000000 : ℝ)*X 1 1+(4578274767/10000000000 : ℝ)*X 1 2+(2184581379/5000000000 : ℝ)*X 2 0+(2084827613/5000000000 : ℝ)*X 2 1+(4578274767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2186651369/10000000000 : ℝ)*X 0 0+(261398609/500000000 : ℝ)*X 0 1+(217348887/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325668557/2500000000 : ℝ)*X 1 0+(-2086195733/10000000000 : ℝ)*X 1 1+(5433722451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302674367/10000000000 : ℝ)*X 2 0+(5433722199/10000000000 : ℝ)*X 2 1+(-2086195889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369203411/10000000000 : ℝ)*X 0 0+(4576632111/10000000000 : ℝ)*X 0 1+(4171307601/10000000000 : ℝ)*X 0 2+(4369203411/10000000000 : ℝ)*X 1 0+(4576632111/10000000000 : ℝ)*X 1 1+(4171307601/10000000000 : ℝ)*X 1 2+(4369203411/10000000000 : ℝ)*X 2 0+(4576632111/10000000000 : ℝ)*X 2 1+(4171307601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6193126555044450414613269573/1954750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214429001/20000000000000 : ℝ)*(base19) + (620140173/100000000000000 : ℝ)*(base23) + (187451371/100000000000000 : ℝ)*(lower2) + (57680761/50000000000000 : ℝ)*(upper5) + (1817093503714989/50000000000000 : ℝ)*(major0) + (1817093503714989/50000000000000 : ℝ)*(major1) + (1817093503714989/50000000000000 : ℝ)*(major2) + (4821072237176669/100000000000000 : ℝ)*(sp0) + (4821093391803643/100000000000000 : ℝ)*(sp1) + (2410547140645189/50000000000000 : ℝ)*(sp2) + (1223635950928209/50000000000000 : ℝ)*(sp3) + (22664253883/100000000000000 : ℝ)*(sp4) + (27342619/6250000000000 : ℝ)*(sp5) + (7105964813/100000000000000 : ℝ)*(sp7) + (152954937988827/6250000000000 : ℝ)*(f.failure) + (4821094901430551/100000000000000 : ℝ)*(f.sum) + (163049482771921/39095000000000000000000000000 : ℝ)*base65 + (29218166704976725603/3909500000000000000000000000000000 : ℝ)*base67 + (21100167894768725603/3909500000000000000000000000000000 : ℝ)*base69 + (34325584332967725603/3909500000000000000000000000000000 : ℝ)*base71 + (128309469995793/19547500000000000000000000000 : ℝ)*base73 + (76365457070893725603/3909500000000000000000000000000000 : ℝ)*base75 + (65558234608479725603/3909500000000000000000000000000000 : ℝ)*base77 + (79833575521725725603/3909500000000000000000000000000000 : ℝ)*base79 + (136433844782281/39095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (74361/39062500000000000000 : ℝ)*base89 + (74361/39062500000000000000 : ℝ)*base91 + (74361/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2092424357985041059425253959/977375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22485707/6250000000000 : ℝ)*(base19) + (633737663/100000000000000 : ℝ)*(base23) + (1516651/2000000000000 : ℝ)*(upper3) + (7255487/10000000000000 : ℝ)*(lower4) + (915928369563287/25000000000000 : ℝ)*(major0) + (915928369563287/25000000000000 : ℝ)*(major1) + (915928369563287/25000000000000 : ℝ)*(major2) + (5387436269/50000000000000 : ℝ)*(sp1) + (11761074751/100000000000000 : ℝ)*(sp2) + (238927737/20000000000000 : ℝ)*(sp3) + (972052921975233/20000000000000 : ℝ)*(sp4) + (2430126737616157/50000000000000 : ℝ)*(sp5) + (4860252215063751/100000000000000 : ℝ)*(sp6) + (493432216125879/20000000000000 : ℝ)*(sp7) + (30839528440851/1250000000000 : ℝ)*(f.failure) + (972052921975233/20000000000000 : ℝ)*(f.sum) + (15849735541517/19547500000000000000000000000 : ℝ)*base66 + (10121981930728913449/1954750000000000000000000000000000 : ℝ)*base67 + (6904578155006413449/1954750000000000000000000000000000 : ℝ)*base69 + (15647655492745913449/1954750000000000000000000000000000 : ℝ)*base71 + (119910051314129/39095000000000000000000000000 : ℝ)*base74 + (16641697228802163449/1954750000000000000000000000000000 : ℝ)*base75 + (21379592916211663449/1954750000000000000000000000000000 : ℝ)*base77 + (1901975721308663449/1954750000000000000000000000000000 : ℝ)*base79 + (265309890367759/39095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (27743/7812500000000000000 : ℝ)*base89 + (27743/7812500000000000000 : ℝ)*base91 + (27743/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1092_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14869/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1092_s4_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547516397/2500000000 : ℝ)*x 0 + (5404403351/10000000000 : ℝ)*x 1 + (262752529/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547516397/2500000000 : ℝ)^8285 ≤ (3325275671377/25000000000000 : ℝ)^6237 := by
    have hnat : (547516397 : ℕ)^8285*25000000000000^6237 ≤ 3325275671377^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547516397 2500000000 3325275671377 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404403351/10000000000 : ℝ)^8285 ≤ (22078116018971/50000000000000 : ℝ)^6237 := by
    have hnat : (5404403351 : ℕ)^8285*50000000000000^6237 ≤ 22078116018971^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404403351 10000000000 22078116018971 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262752529/500000000 : ℝ)^8285 ≤ (42542665265953/100000000000000 : ℝ)^6237 := by
    have hnat : (262752529 : ℕ)^8285*100000000000000^6237 ≤ 42542665265953^6237*500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262752529 500000000 42542665265953 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547516397/2500000000 : ℝ), (5404403351/10000000000 : ℝ), (262752529/500000000 : ℝ)] ![(3325275671377/25000000000000 : ℝ), (22078116018971/50000000000000 : ℝ), (42542665265953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547516397/2500000000 : ℝ)|^8285 ≤ (3325275671377/25000000000000 : ℝ)^6237
        have hw : |(-547516397/2500000000 : ℝ)|=(547516397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404403351/10000000000 : ℝ)|^8285 ≤ (22078116018971/50000000000000 : ℝ)^6237
        have hw : |(5404403351/10000000000 : ℝ)|=(5404403351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262752529/500000000 : ℝ)|^8285 ≤ (42542665265953/100000000000000 : ℝ)^6237
        have hw : |(262752529/500000000 : ℝ)|=(262752529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673767777/5000000000 : ℝ)*x 0 + (-2266007619/10000000000 : ℝ)*x 1 + (5255050389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673767777/5000000000 : ℝ)^8285 ≤ (43540098695393/100000000000000 : ℝ)^6237 := by
    have hnat : (2673767777 : ℕ)^8285*100000000000000^6237 ≤ 43540098695393^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673767777 5000000000 43540098695393 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266007619/10000000000 : ℝ)^8285 ≤ (13917238083159/100000000000000 : ℝ)^6237 := by
    have hnat : (2266007619 : ℕ)^8285*100000000000000^6237 ≤ 13917238083159^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266007619 10000000000 13917238083159 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255050389/10000000000 : ℝ)^8285 ≤ (8508532642393/20000000000000 : ℝ)^6237 := by
    have hnat : (5255050389 : ℕ)^8285*20000000000000^6237 ≤ 8508532642393^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255050389 10000000000 8508532642393 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673767777/5000000000 : ℝ), (-2266007619/10000000000 : ℝ), (5255050389/10000000000 : ℝ)] ![(43540098695393/100000000000000 : ℝ), (13917238083159/100000000000000 : ℝ), (8508532642393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673767777/5000000000 : ℝ)|^8285 ≤ (43540098695393/100000000000000 : ℝ)^6237
        have hw : |(2673767777/5000000000 : ℝ)|=(2673767777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2266007619/10000000000 : ℝ)|^8285 ≤ (13917238083159/100000000000000 : ℝ)^6237
        have hw : |(-2266007619/10000000000 : ℝ)|=(2266007619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255050389/10000000000 : ℝ)|^8285 ≤ (8508532642393/20000000000000 : ℝ)^6237
        have hw : |(5255050389/10000000000 : ℝ)|=(5255050389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347535843/10000000000 : ℝ)*x 0 + (210202013/400000000 : ℝ)*x 1 + (-2266007319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347535843/10000000000 : ℝ)^8285 ≤ (8708020364223/20000000000000 : ℝ)^6237 := by
    have hnat : (5347535843 : ℕ)^8285*20000000000000^6237 ≤ 8708020364223^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347535843 10000000000 8708020364223 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210202013/400000000 : ℝ)^8285 ≤ (21271331261859/50000000000000 : ℝ)^6237 := by
    have hnat : (210202013 : ℕ)^8285*50000000000000^6237 ≤ 21271331261859^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210202013 400000000 21271331261859 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266007319/10000000000 : ℝ)^8285 ≤ (695861781781/5000000000000 : ℝ)^6237 := by
    have hnat : (2266007319 : ℕ)^8285*5000000000000^6237 ≤ 695861781781^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266007319 10000000000 695861781781 5000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347535843/10000000000 : ℝ), (210202013/400000000 : ℝ), (-2266007319/10000000000 : ℝ)] ![(8708020364223/20000000000000 : ℝ), (21271331261859/50000000000000 : ℝ), (695861781781/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347535843/10000000000 : ℝ)|^8285 ≤ (8708020364223/20000000000000 : ℝ)^6237
        have hw : |(5347535843/10000000000 : ℝ)|=(5347535843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210202013/400000000 : ℝ)|^8285 ≤ (21271331261859/50000000000000 : ℝ)^6237
        have hw : |(210202013/400000000 : ℝ)|=(210202013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266007319/10000000000 : ℝ)|^8285 ≤ (695861781781/5000000000000 : ℝ)^6237
        have hw : |(-2266007319/10000000000 : ℝ)|=(2266007319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371206589/10000000000 : ℝ)*x 0 + (422658687/1000000000 : ℝ)*x 1 + (1130202319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371206589/10000000000 : ℝ)^8285 ≤ (4163879208183/12500000000000 : ℝ)^6237 := by
    have hnat : (4371206589 : ℕ)^8285*12500000000000^6237 ≤ 4163879208183^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371206589 10000000000 4163879208183 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422658687/1000000000 : ℝ)^8285 ≤ (1592753962857/5000000000000 : ℝ)^6237 := by
    have hnat : (422658687 : ℕ)^8285*5000000000000^6237 ≤ 1592753962857^6237*1000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422658687 1000000000 1592753962857 5000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130202319/2500000000 : ℝ)^8285 ≤ (8708471764547/25000000000000 : ℝ)^6237 := by
    have hnat : (1130202319 : ℕ)^8285*25000000000000^6237 ≤ 8708471764547^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130202319 2500000000 8708471764547 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371206589/10000000000 : ℝ), (422658687/1000000000 : ℝ), (1130202319/2500000000 : ℝ)] ![(4163879208183/12500000000000 : ℝ), (1592753962857/5000000000000 : ℝ), (8708471764547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371206589/10000000000 : ℝ)|^8285 ≤ (4163879208183/12500000000000 : ℝ)^6237
        have hw : |(4371206589/10000000000 : ℝ)|=(4371206589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422658687/1000000000 : ℝ)|^8285 ≤ (1592753962857/5000000000000 : ℝ)^6237
        have hw : |(422658687/1000000000 : ℝ)|=(422658687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130202319/2500000000 : ℝ)|^8285 ≤ (8708471764547/25000000000000 : ℝ)^6237
        have hw : |(1130202319/2500000000 : ℝ)|=(1130202319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109503689/500000000 : ℝ)*x 0 + (5255483663/10000000000 : ℝ)*x 1 + (2701984067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109503689/500000000 : ℝ)^8285 ≤ (532046751031/4000000000000 : ℝ)^6237 := by
    have hnat : (109503689 : ℕ)^8285*4000000000000^6237 ≤ 532046751031^6237*500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109503689 500000000 532046751031 4000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255483663/10000000000 : ℝ)^8285 ≤ (21273661322449/50000000000000 : ℝ)^6237 := by
    have hnat : (5255483663 : ℕ)^8285*50000000000000^6237 ≤ 21273661322449^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255483663 10000000000 21273661322449 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701984067/5000000000 : ℝ)^8285 ≤ (22075754284143/50000000000000 : ℝ)^6237 := by
    have hnat : (2701984067 : ℕ)^8285*50000000000000^6237 ≤ 22075754284143^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701984067 5000000000 22075754284143 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109503689/500000000 : ℝ), (5255483663/10000000000 : ℝ), (2701984067/5000000000 : ℝ)] ![(532046751031/4000000000000 : ℝ), (21273661322449/50000000000000 : ℝ), (22075754284143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109503689/500000000 : ℝ)|^8285 ≤ (532046751031/4000000000000 : ℝ)^6237
        have hw : |(-109503689/500000000 : ℝ)|=(109503689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255483663/10000000000 : ℝ)|^8285 ≤ (21273661322449/50000000000000 : ℝ)^6237
        have hw : |(5255483663/10000000000 : ℝ)|=(5255483663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701984067/5000000000 : ℝ)|^8285 ≤ (22075754284143/50000000000000 : ℝ)^6237
        have hw : |(2701984067/5000000000 : ℝ)|=(2701984067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309841953/10000000000 : ℝ)*x 0 + (-2117089129/10000000000 : ℝ)*x 1 + (2701984147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309841953/10000000000 : ℝ)^8285 ≤ (43132890566739/100000000000000 : ℝ)^6237 := by
    have hnat : (5309841953 : ℕ)^8285*100000000000000^6237 ≤ 43132890566739^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309841953 10000000000 43132890566739 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117089129/10000000000 : ℝ)^8285 ≤ (1589449889137/12500000000000 : ℝ)^6237 := by
    have hnat : (2117089129 : ℕ)^8285*12500000000000^6237 ≤ 1589449889137^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117089129 10000000000 1589449889137 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701984147/5000000000 : ℝ)^8285 ≤ (8830302060953/20000000000000 : ℝ)^6237 := by
    have hnat : (2701984147 : ℕ)^8285*20000000000000^6237 ≤ 8830302060953^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701984147 5000000000 8830302060953 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309841953/10000000000 : ℝ), (-2117089129/10000000000 : ℝ), (2701984147/5000000000 : ℝ)] ![(43132890566739/100000000000000 : ℝ), (1589449889137/12500000000000 : ℝ), (8830302060953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309841953/10000000000 : ℝ)|^8285 ≤ (43132890566739/100000000000000 : ℝ)^6237
        have hw : |(5309841953/10000000000 : ℝ)|=(5309841953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117089129/10000000000 : ℝ)|^8285 ≤ (1589449889137/12500000000000 : ℝ)^6237
        have hw : |(-2117089129/10000000000 : ℝ)|=(2117089129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701984147/5000000000 : ℝ)|^8285 ≤ (8830302060953/20000000000000 : ℝ)^6237
        have hw : |(2701984147/5000000000 : ℝ)|=(2701984147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309841729/10000000000 : ℝ)*x 0 + (5403968361/10000000000 : ℝ)*x 1 + (-2117089341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309841729/10000000000 : ℝ)^8285 ≤ (8626577629931/20000000000000 : ℝ)^6237 := by
    have hnat : (5309841729 : ℕ)^8285*20000000000000^6237 ≤ 8626577629931^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309841729 10000000000 8626577629931 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403968361/10000000000 : ℝ)^8285 ≤ (8830302206383/20000000000000 : ℝ)^6237 := by
    have hnat : (5403968361 : ℕ)^8285*20000000000000^6237 ≤ 8830302206383^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403968361 10000000000 8830302206383 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117089341/10000000000 : ℝ)^8285 ≤ (12715600804511/100000000000000 : ℝ)^6237 := by
    have hnat : (2117089341 : ℕ)^8285*100000000000000^6237 ≤ 12715600804511^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117089341 10000000000 12715600804511 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309841729/10000000000 : ℝ), (5403968361/10000000000 : ℝ), (-2117089341/10000000000 : ℝ)] ![(8626577629931/20000000000000 : ℝ), (8830302206383/20000000000000 : ℝ), (12715600804511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309841729/10000000000 : ℝ)|^8285 ≤ (8626577629931/20000000000000 : ℝ)^6237
        have hw : |(5309841729/10000000000 : ℝ)|=(5309841729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403968361/10000000000 : ℝ)|^8285 ≤ (8830302206383/20000000000000 : ℝ)^6237
        have hw : |(5403968361/10000000000 : ℝ)|=(5403968361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117089341/10000000000 : ℝ)|^8285 ≤ (12715600804511/100000000000000 : ℝ)^6237
        have hw : |(-2117089341/10000000000 : ℝ)|=(2117089341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s4_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437122181/1000000000 : ℝ)*x 0 + (4519955681/10000000000 : ℝ)*x 1 + (1056861023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437122181/1000000000 : ℝ)^8285 ≤ (8327796936429/25000000000000 : ℝ)^6237 := by
    have hnat : (437122181 : ℕ)^8285*25000000000000^6237 ≤ 8327796936429^6237*1000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437122181 1000000000 8327796936429 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519955681/10000000000 : ℝ)^8285 ≤ (6965030097797/20000000000000 : ℝ)^6237 := by
    have hnat : (4519955681 : ℕ)^8285*20000000000000^6237 ≤ 6965030097797^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519955681 10000000000 6965030097797 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056861023/2500000000 : ℝ)^8285 ≤ (637273234991/2000000000000 : ℝ)^6237 := by
    have hnat : (1056861023 : ℕ)^8285*2000000000000^6237 ≤ 637273234991^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056861023 2500000000 637273234991 2000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437122181/1000000000 : ℝ), (4519955681/10000000000 : ℝ), (1056861023/2500000000 : ℝ)] ![(8327796936429/25000000000000 : ℝ), (6965030097797/20000000000000 : ℝ), (637273234991/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437122181/1000000000 : ℝ)|^8285 ≤ (8327796936429/25000000000000 : ℝ)^6237
        have hw : |(437122181/1000000000 : ℝ)|=(437122181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519955681/10000000000 : ℝ)|^8285 ≤ (6965030097797/20000000000000 : ℝ)^6237
        have hw : |(4519955681/10000000000 : ℝ)|=(4519955681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056861023/2500000000 : ℝ)|^8285 ≤ (637273234991/2000000000000 : ℝ)^6237
        have hw : |(1056861023/2500000000 : ℝ)|=(1056861023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10481/100000 : ℝ) ^ (2071/512 : ℝ) ≤ (5452247245468383/50000000000000000000 : ℝ) := by
    have hpowers : (10481/100000 : ℝ)^2071 ≤ (5452247245468383/50000000000000000000 : ℝ)^512 := by
      have hnat : (10481 : ℕ)^2071*50000000000000000000^512 ≤ 5452247245468383^512*100000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10481 100000 5452247245468383 50000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10481/100000 : ℝ)) (X := (5452247245468383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14869/100000 : ℝ) ^ (2071/512 : ℝ) ≤ (11217198345293099/25000000000000000000 : ℝ) := by
    have hpowers : (14869/100000 : ℝ)^2071 ≤ (11217198345293099/25000000000000000000 : ℝ)^512 := by
      have hnat : (14869 : ℕ)^2071*25000000000000000000^512 ≤ 11217198345293099^512*100000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14869 100000 11217198345293099 25000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14869/100000 : ℝ)) (X := (11217198345293099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005452247245468383/25000000000000000000 : ℝ) ≤ (10000539125344347/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25005452247245468383/25000000000000000000 : ℝ)^512 ≤ (10000539125344347/10000000000000000 : ℝ)^2071 := by
      have hnat : (25005452247245468383 : ℕ)^512*10000000000000000^2071 ≤ 10000539125344347^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005452247245468383 25000000000000000000 10000539125344347 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539125344347/10000000000000000 : ℝ)) (X := (25005452247245468383/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027886643936054581/50000000000000000000 : ℝ) ≤ (5000689278869317/5000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (50027886643936054581/50000000000000000000 : ℝ)^512 ≤ (5000689278869317/5000000000000000 : ℝ)^2071 := by
      have hnat : (50027886643936054581 : ℕ)^512*5000000000000000^2071 ≤ 5000689278869317^2071*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027886643936054581 50000000000000000000 5000689278869317 5000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000689278869317/5000000000000000 : ℝ)) (X := (50027886643936054581/50000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511217198345293099/12500000000000000000 : ℝ) ≤ (10002217990132921/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (12511217198345293099/12500000000000000000 : ℝ)^512 ≤ (10002217990132921/10000000000000000 : ℝ)^2071 := by
      have hnat : (12511217198345293099 : ℕ)^512*10000000000000000^2071 ≤ 10002217990132921^2071*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511217198345293099 12500000000000000000 10002217990132921 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002217990132921/10000000000000000 : ℝ)) (X := (12511217198345293099/12500000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5452247245468383/50000000000000000000 : ℝ) ≤ ((21932384750080975271/21940000000000000000 : ℝ)+2*(839432394287/438800000000000 : ℝ)*(10481/100000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (21932384750080975271/21940000000000000000 : ℝ)+2*(839432394287/438800000000000 : ℝ)*(10481/100000 : ℝ)=(10000539125344347/10000000000000000 : ℝ) by norm_num, show 1+2*(5452247245468383/50000000000000000000 : ℝ)=(25005452247245468383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11217198345293099/25000000000000000000 : ℝ)+(5452247245468383/50000000000000000000 : ℝ) ≤ ((21932384750080975271/21940000000000000000 : ℝ)+(839432394287/438800000000000 : ℝ)*((14869/100000 : ℝ)+(10481/100000 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (21932384750080975271/21940000000000000000 : ℝ)+(839432394287/438800000000000 : ℝ)*((14869/100000 : ℝ)+(10481/100000 : ℝ))=(5000689278869317/5000000000000000 : ℝ) by norm_num, show 1+(11217198345293099/25000000000000000000 : ℝ)+(5452247245468383/50000000000000000000 : ℝ)=(50027886643936054581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11217198345293099/25000000000000000000 : ℝ) ≤ ((21932384750080975271/21940000000000000000 : ℝ)+2*(839432394287/438800000000000 : ℝ)*(14869/100000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (21932384750080975271/21940000000000000000 : ℝ)+2*(839432394287/438800000000000 : ℝ)*(14869/100000 : ℝ)=(10002217990132921/10000000000000000 : ℝ) by norm_num, show 1+2*(11217198345293099/25000000000000000000 : ℝ)=(12511217198345293099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21932384750080975271/21940000000000000000 : ℝ)*(X 1 0+X 2 0)+(839432394287/438800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (14869/100000 : ℝ)) (c := (21932384750080975271/21940000000000000000 : ℝ)) (alpha := (839432394287/438800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21932384750080975271/21940000000000000000 : ℝ)*(X 0 1+X 2 1)+(839432394287/438800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (14869/100000 : ℝ)) (c := (21932384750080975271/21940000000000000000 : ℝ)) (alpha := (839432394287/438800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21932384750080975271/21940000000000000000 : ℝ)*(X 0 2+X 1 2)+(839432394287/438800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (14869/100000 : ℝ)) (c := (21932384750080975271/21940000000000000000 : ℝ)) (alpha := (839432394287/438800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-547516397/2500000000 : ℝ)*X 0 0+(5404403351/10000000000 : ℝ)*X 0 1+(262752529/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673767777/5000000000 : ℝ)*X 1 0+(-2266007619/10000000000 : ℝ)*X 1 1+(5255050389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347535843/10000000000 : ℝ)*X 2 0+(210202013/400000000 : ℝ)*X 2 1+(-2266007319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371206589/10000000000 : ℝ)*X 0 0+(422658687/1000000000 : ℝ)*X 0 1+(1130202319/2500000000 : ℝ)*X 0 2+(4371206589/10000000000 : ℝ)*X 1 0+(422658687/1000000000 : ℝ)*X 1 1+(1130202319/2500000000 : ℝ)*X 1 2+(4371206589/10000000000 : ℝ)*X 2 0+(422658687/1000000000 : ℝ)*X 2 1+(1130202319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109503689/500000000 : ℝ)*X 0 0+(5255483663/10000000000 : ℝ)*X 0 1+(2701984067/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309841953/10000000000 : ℝ)*X 1 0+(-2117089129/10000000000 : ℝ)*X 1 1+(2701984147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309841729/10000000000 : ℝ)*X 2 0+(5403968361/10000000000 : ℝ)*X 2 1+(-2117089341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437122181/1000000000 : ℝ)*X 0 0+(4519955681/10000000000 : ℝ)*X 0 1+(1056861023/2500000000 : ℝ)*X 0 2+(437122181/1000000000 : ℝ)*X 1 0+(4519955681/10000000000 : ℝ)*X 1 1+(1056861023/2500000000 : ℝ)*X 1 2+(437122181/1000000000 : ℝ)*X 2 0+(4519955681/10000000000 : ℝ)*X 2 1+(1056861023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5409105267968669821065012501/1097000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46242449/50000000000000 : ℝ)*(base8) + (75488711/100000000000000 : ℝ)*(base21) + (141176249/50000000000000 : ℝ)*(lower2) + (33284159/100000000000000 : ℝ)*(lower4) + (5047166329912459/100000000000000 : ℝ)*(major0) + (5047166329912459/100000000000000 : ℝ)*(major1) + (5047166329912459/100000000000000 : ℝ)*(major2) + (334777311198349/5000000000000 : ℝ)*(sp0) + (1673885248117007/25000000000000 : ℝ)*(sp1) + (1673886585323629/25000000000000 : ℝ)*(sp2) + (1699392707427011/50000000000000 : ℝ)*(sp3) + (2006627/2000000000000 : ℝ)*(sp4) + (3390197/62500000000 : ℝ)*(sp5) + (663827121/100000000000000 : ℝ)*(sp7) + (1699393039340571/50000000000000 : ℝ)*(f.failure) + (1673886604195807/25000000000000 : ℝ)*(f.sum) + (144491940069413/21940000000000000000000000000 : ℝ)*base65 + (16432848579913548611/2194000000000000000000000000000000 : ℝ)*base68 + (13700607576915548611/2194000000000000000000000000000000 : ℝ)*base70 + (2631519024659548611/2194000000000000000000000000000000 : ℝ)*base72 + (25222224311727/21940000000000000000000000000 : ℝ)*base74 + (30556412744963548611/2194000000000000000000000000000000 : ℝ)*base76 + (33644770648603548611/2194000000000000000000000000000000 : ℝ)*base78 + (1490463857893548611/2194000000000000000000000000000000 : ℝ)*base80 + (81551313602267/21940000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2193797/312500000000000000000 : ℝ)*base90 + (2193797/312500000000000000000 : ℝ)*base92 + (2193797/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5361539412152439953308709811/1097000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1076567563/100000000000000 : ℝ)*(base19) + (108730509/12500000000000 : ℝ)*(base23) + (13023319/25000000000000 : ℝ)*(upper3) + (76084903/100000000000000 : ℝ)*(lower4) + (89819903/100000000000000 : ℝ)*(upper5) + (5076686390081753/100000000000000 : ℝ)*(major0) + (5076686390081753/100000000000000 : ℝ)*(major1) + (5076686390081753/100000000000000 : ℝ)*(major2) + (18481857859/50000000000000 : ℝ)*(sp1) + (27679434553/100000000000000 : ℝ)*(sp2) + (6734707588085453/100000000000000 : ℝ)*(sp4) + (6734669547802173/100000000000000 : ℝ)*(sp5) + (6734679038806827/100000000000000 : ℝ)*(sp6) + (3418665029162841/100000000000000 : ℝ)*(sp7) + (3418665029162841/100000000000000 : ℝ)*(f.failure) + (6734707588085453/100000000000000 : ℝ)*(f.sum) + (21973945397311/21940000000000000000000000000 : ℝ)*base65 + (5140322331276880063/2194000000000000000000000000000000 : ℝ)*base67 + (14840356116560880063/2194000000000000000000000000000000 : ℝ)*base69 + (17364105650177119937/2194000000000000000000000000000000 : ℝ)*base72 + (56922673998831/21940000000000000000000000000 : ℝ)*base73 + (422561325067119937/2194000000000000000000000000000000 : ℝ)*base76 + (5845638016148880063/2194000000000000000000000000000000 : ℝ)*base77 + (35487234634274880063/2194000000000000000000000000000000 : ℝ)*base79 + (35204351273409/21940000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (500687/625000000000000000000 : ℝ)*base90 + (500687/625000000000000000000 : ℝ)*base92 + (500687/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1092_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1092_s5_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273852833/1250000000 : ℝ)*x 0 + (5396258857/10000000000 : ℝ)*x 1 + (5262698507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273852833/1250000000 : ℝ)^8285 ≤ (13307210859767/100000000000000 : ℝ)^6237 := by
    have hnat : (273852833 : ℕ)^8285*100000000000000^6237 ≤ 13307210859767^6237*1250000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273852833 1250000000 13307210859767 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396258857/10000000000 : ℝ)^8285 ≤ (44067859439567/100000000000000 : ℝ)^6237 := by
    have hnat : (5396258857 : ℕ)^8285*100000000000000^6237 ≤ 44067859439567^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396258857 10000000000 44067859439567 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262698507/10000000000 : ℝ)^8285 ≤ (42624929682423/100000000000000 : ℝ)^6237 := by
    have hnat : (5262698507 : ℕ)^8285*100000000000000^6237 ≤ 42624929682423^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262698507 10000000000 42624929682423 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273852833/1250000000 : ℝ), (5396258857/10000000000 : ℝ), (5262698507/10000000000 : ℝ)] ![(13307210859767/100000000000000 : ℝ), (44067859439567/100000000000000 : ℝ), (42624929682423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273852833/1250000000 : ℝ)|^8285 ≤ (13307210859767/100000000000000 : ℝ)^6237
        have hw : |(-273852833/1250000000 : ℝ)|=(273852833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396258857/10000000000 : ℝ)|^8285 ≤ (44067859439567/100000000000000 : ℝ)^6237
        have hw : |(5396258857/10000000000 : ℝ)|=(5396258857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262698507/10000000000 : ℝ)|^8285 ≤ (42624929682423/100000000000000 : ℝ)^6237
        have hw : |(5262698507/10000000000 : ℝ)|=(5262698507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336376009/2500000000 : ℝ)*x 0 + (-2258616387/10000000000 : ℝ)*x 1 + (5262696009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336376009/2500000000 : ℝ)^8285 ≤ (1359941496399/3125000000000 : ℝ)^6237 := by
    have hnat : (1336376009 : ℕ)^8285*3125000000000^6237 ≤ 1359941496399^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336376009 2500000000 1359941496399 3125000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258616387/10000000000 : ℝ)^8285 ≤ (3464242322811/25000000000000 : ℝ)^6237 := by
    have hnat : (2258616387 : ℕ)^8285*25000000000000^6237 ≤ 3464242322811^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258616387 10000000000 3464242322811 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262696009/10000000000 : ℝ)^8285 ≤ (1065622570161/2500000000000 : ℝ)^6237 := by
    have hnat : (5262696009 : ℕ)^8285*2500000000000^6237 ≤ 1065622570161^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262696009 10000000000 1065622570161 2500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336376009/2500000000 : ℝ), (-2258616387/10000000000 : ℝ), (5262696009/10000000000 : ℝ)] ![(1359941496399/3125000000000 : ℝ), (3464242322811/25000000000000 : ℝ), (1065622570161/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336376009/2500000000 : ℝ)|^8285 ≤ (1359941496399/3125000000000 : ℝ)^6237
        have hw : |(1336376009/2500000000 : ℝ)|=(1336376009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258616387/10000000000 : ℝ)|^8285 ≤ (3464242322811/25000000000000 : ℝ)^6237
        have hw : |(-2258616387/10000000000 : ℝ)|=(2258616387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262696009/10000000000 : ℝ)|^8285 ≤ (1065622570161/2500000000000 : ℝ)^6237
        have hw : |(5262696009/10000000000 : ℝ)|=(5262696009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106910069/200000000 : ℝ)*x 0 + (2631348861/5000000000 : ℝ)*x 1 + (-2258614903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106910069/200000000 : ℝ)^8285 ≤ (43518121547589/100000000000000 : ℝ)^6237 := by
    have hnat : (106910069 : ℕ)^8285*100000000000000^6237 ≤ 43518121547589^6237*200000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106910069 200000000 43518121547589 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631348861/5000000000 : ℝ)^8285 ≤ (42624921236607/100000000000000 : ℝ)^6237 := by
    have hnat : (2631348861 : ℕ)^8285*100000000000000^6237 ≤ 42624921236607^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631348861 5000000000 42624921236607 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258614903/10000000000 : ℝ)^8285 ≤ (2771391439413/20000000000000 : ℝ)^6237 := by
    have hnat : (2258614903 : ℕ)^8285*20000000000000^6237 ≤ 2771391439413^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258614903 10000000000 2771391439413 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106910069/200000000 : ℝ), (2631348861/5000000000 : ℝ), (-2258614903/10000000000 : ℝ)] ![(43518121547589/100000000000000 : ℝ), (42624921236607/100000000000000 : ℝ), (2771391439413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106910069/200000000 : ℝ)|^8285 ≤ (43518121547589/100000000000000 : ℝ)^6237
        have hw : |(106910069/200000000 : ℝ)|=(106910069/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631348861/5000000000 : ℝ)|^8285 ≤ (42624921236607/100000000000000 : ℝ)^6237
        have hw : |(2631348861/5000000000 : ℝ)|=(2631348861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2258614903/10000000000 : ℝ)|^8285 ≤ (2771391439413/20000000000000 : ℝ)^6237
        have hw : |(-2258614903/10000000000 : ℝ)|=(2258614903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371647289/10000000000 : ℝ)*x 0 + (4242083679/10000000000 : ℝ)*x 1 + (2252598657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371647289/10000000000 : ℝ)^8285 ≤ (16657747443473/50000000000000 : ℝ)^6237 := by
    have hnat : (4371647289 : ℕ)^8285*50000000000000^6237 ≤ 16657747443473^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371647289 10000000000 16657747443473 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242083679/10000000000 : ℝ)^8285 ≤ (1280412848153/4000000000000 : ℝ)^6237 := by
    have hnat : (4242083679 : ℕ)^8285*4000000000000^6237 ≤ 1280412848153^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242083679 10000000000 1280412848153 4000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252598657/5000000000 : ℝ)^8285 ≤ (8668545974259/25000000000000 : ℝ)^6237 := by
    have hnat : (2252598657 : ℕ)^8285*25000000000000^6237 ≤ 8668545974259^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252598657 5000000000 8668545974259 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371647289/10000000000 : ℝ), (4242083679/10000000000 : ℝ), (2252598657/5000000000 : ℝ)] ![(16657747443473/50000000000000 : ℝ), (1280412848153/4000000000000 : ℝ), (8668545974259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371647289/10000000000 : ℝ)|^8285 ≤ (16657747443473/50000000000000 : ℝ)^6237
        have hw : |(4371647289/10000000000 : ℝ)|=(4371647289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242083679/10000000000 : ℝ)|^8285 ≤ (1280412848153/4000000000000 : ℝ)^6237
        have hw : |(4242083679/10000000000 : ℝ)|=(4242083679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252598657/5000000000 : ℝ)|^8285 ≤ (8668545974259/25000000000000 : ℝ)^6237
        have hw : |(2252598657/5000000000 : ℝ)|=(2252598657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095414221/5000000000 : ℝ)*x 0 + (2631522169/5000000000 : ℝ)*x 1 + (1079182311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095414221/5000000000 : ℝ)^8285 ≤ (6653628739993/50000000000000 : ℝ)^6237 := by
    have hnat : (1095414221 : ℕ)^8285*50000000000000^6237 ≤ 6653628739993^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095414221 5000000000 6653628739993 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631522169/5000000000 : ℝ)^8285 ≤ (4262865051869/10000000000000 : ℝ)^6237 := by
    have hnat : (2631522169 : ℕ)^8285*10000000000000^6237 ≤ 4262865051869^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631522169 5000000000 4262865051869 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079182311/2000000000 : ℝ)^8285 ≤ (11016022994903/25000000000000 : ℝ)^6237 := by
    have hnat : (1079182311 : ℕ)^8285*25000000000000^6237 ≤ 11016022994903^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079182311 2000000000 11016022994903 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095414221/5000000000 : ℝ), (2631522169/5000000000 : ℝ), (1079182311/2000000000 : ℝ)] ![(6653628739993/50000000000000 : ℝ), (4262865051869/10000000000000 : ℝ), (11016022994903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095414221/5000000000 : ℝ)|^8285 ≤ (6653628739993/50000000000000 : ℝ)^6237
        have hw : |(-1095414221/5000000000 : ℝ)|=(1095414221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631522169/5000000000 : ℝ)|^8285 ≤ (4262865051869/10000000000000 : ℝ)^6237
        have hw : |(2631522169/5000000000 : ℝ)|=(2631522169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079182311/2000000000 : ℝ)|^8285 ≤ (11016022994903/25000000000000 : ℝ)^6237
        have hw : |(1079182311/2000000000 : ℝ)|=(1079182311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655896573/5000000000 : ℝ)*x 0 + (-1062700791/5000000000 : ℝ)*x 1 + (5395911557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655896573/5000000000 : ℝ)^8285 ≤ (21576973145039/50000000000000 : ℝ)^6237 := by
    have hnat : (2655896573 : ℕ)^8285*50000000000000^6237 ≤ 21576973145039^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655896573 5000000000 21576973145039 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062700791/5000000000 : ℝ)^8285 ≤ (1278196169627/10000000000000 : ℝ)^6237 := by
    have hnat : (1062700791 : ℕ)^8285*10000000000000^6237 ≤ 1278196169627^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062700791 5000000000 1278196169627 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395911557/10000000000 : ℝ)^8285 ≤ (44064092001307/100000000000000 : ℝ)^6237 := by
    have hnat : (5395911557 : ℕ)^8285*100000000000000^6237 ≤ 44064092001307^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395911557 10000000000 44064092001307 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655896573/5000000000 : ℝ), (-1062700791/5000000000 : ℝ), (5395911557/10000000000 : ℝ)] ![(21576973145039/50000000000000 : ℝ), (1278196169627/10000000000000 : ℝ), (44064092001307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655896573/5000000000 : ℝ)|^8285 ≤ (21576973145039/50000000000000 : ℝ)^6237
        have hw : |(2655896573/5000000000 : ℝ)|=(2655896573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062700791/5000000000 : ℝ)|^8285 ≤ (1278196169627/10000000000000 : ℝ)^6237
        have hw : |(-1062700791/5000000000 : ℝ)|=(1062700791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395911557/10000000000 : ℝ)|^8285 ≤ (44064092001307/100000000000000 : ℝ)^6237
        have hw : |(5395911557/10000000000 : ℝ)|=(5395911557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327948291/2500000000 : ℝ)*x 0 + (107918231/200000000 : ℝ)*x 1 + (-2125401567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327948291/2500000000 : ℝ)^8285 ≤ (43153946484331/100000000000000 : ℝ)^6237 := by
    have hnat : (1327948291 : ℕ)^8285*100000000000000^6237 ≤ 43153946484331^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327948291 2500000000 43153946484331 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107918231/200000000 : ℝ)^8285 ≤ (44064091925373/100000000000000 : ℝ)^6237 := by
    have hnat : (107918231 : ℕ)^8285*100000000000000^6237 ≤ 44064091925373^6237*200000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107918231 200000000 44064091925373 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125401567/10000000000 : ℝ)^8285 ≤ (319549039411/2500000000000 : ℝ)^6237 := by
    have hnat : (2125401567 : ℕ)^8285*2500000000000^6237 ≤ 319549039411^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125401567 10000000000 319549039411 2500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327948291/2500000000 : ℝ), (107918231/200000000 : ℝ), (-2125401567/10000000000 : ℝ)] ![(43153946484331/100000000000000 : ℝ), (44064091925373/100000000000000 : ℝ), (319549039411/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327948291/2500000000 : ℝ)|^8285 ≤ (43153946484331/100000000000000 : ℝ)^6237
        have hw : |(1327948291/2500000000 : ℝ)|=(1327948291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107918231/200000000 : ℝ)|^8285 ≤ (44064091925373/100000000000000 : ℝ)^6237
        have hw : |(107918231/200000000 : ℝ)|=(107918231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125401567/10000000000 : ℝ)|^8285 ≤ (319549039411/2500000000000 : ℝ)^6237
        have hw : |(-2125401567/10000000000 : ℝ)|=(2125401567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s5_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371658431/10000000000 : ℝ)*x 0 + (563064337/1250000000 : ℝ)*x 1 + (4242768631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371658431/10000000000 : ℝ)^8285 ≤ (6663121535943/20000000000000 : ℝ)^6237 := by
    have hnat : (4371658431 : ℕ)^8285*20000000000000^6237 ≤ 6663121535943^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371658431 10000000000 6663121535943 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563064337/1250000000 : ℝ)^8285 ≤ (34667205171279/100000000000000 : ℝ)^6237 := by
    have hnat : (563064337 : ℕ)^8285*100000000000000^6237 ≤ 34667205171279^6237*1250000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563064337 1250000000 34667205171279 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242768631/10000000000 : ℝ)^8285 ≤ (6403437426287/20000000000000 : ℝ)^6237 := by
    have hnat : (4242768631 : ℕ)^8285*20000000000000^6237 ≤ 6403437426287^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242768631 10000000000 6403437426287 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371658431/10000000000 : ℝ), (563064337/1250000000 : ℝ), (4242768631/10000000000 : ℝ)] ![(6663121535943/20000000000000 : ℝ), (34667205171279/100000000000000 : ℝ), (6403437426287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371658431/10000000000 : ℝ)|^8285 ≤ (6663121535943/20000000000000 : ℝ)^6237
        have hw : |(4371658431/10000000000 : ℝ)|=(4371658431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563064337/1250000000 : ℝ)|^8285 ≤ (34667205171279/100000000000000 : ℝ)^6237
        have hw : |(563064337/1250000000 : ℝ)|=(563064337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242768631/10000000000 : ℝ)|^8285 ≤ (6403437426287/20000000000000 : ℝ)^6237
        have hw : |(4242768631/10000000000 : ℝ)|=(4242768631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11077/100000 : ℝ) ^ (2071/512 : ℝ) ≤ (6819181953572377/50000000000000000000 : ℝ) := by
    have hpowers : (11077/100000 : ℝ)^2071 ≤ (6819181953572377/50000000000000000000 : ℝ)^512 := by
      have hnat : (11077 : ℕ)^2071*50000000000000000000^512 ≤ 6819181953572377^512*100000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11077 100000 6819181953572377 50000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11077/100000 : ℝ)) (X := (6819181953572377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (2071/512 : ℝ) ≤ (37660898023895853/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^2071 ≤ (37660898023895853/100000000000000000000 : ℝ)^512 := by
      have hnat : (14239 : ℕ)^2071*100000000000000000000^512 ≤ 37660898023895853^512*100000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 37660898023895853 100000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (37660898023895853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006819181953572377/25000000000000000000 : ℝ) ≤ (5000337137881771/5000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25006819181953572377/25000000000000000000 : ℝ)^512 ≤ (5000337137881771/5000000000000000 : ℝ)^2071 := by
      have hnat : (25006819181953572377 : ℕ)^512*5000000000000000^2071 ≤ 5000337137881771^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006819181953572377 25000000000000000000 5000337137881771 5000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337137881771/5000000000000000 : ℝ)) (X := (25006819181953572377/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051299261931040607/100000000000000000000 : ℝ) ≤ (1250158499228779/1250000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (100051299261931040607/100000000000000000000 : ℝ)^512 ≤ (1250158499228779/1250000000000000 : ℝ)^2071 := by
      have hnat : (100051299261931040607 : ℕ)^512*1250000000000000^2071 ≤ 1250158499228779^2071*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051299261931040607 100000000000000000000 1250158499228779 1250000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250158499228779/1250000000000000 : ℝ)) (X := (100051299261931040607/100000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037660898023895853/50000000000000000000 : ℝ) ≤ (5000930855948461/5000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (50037660898023895853/50000000000000000000 : ℝ)^512 ≤ (5000930855948461/5000000000000000 : ℝ)^2071 := by
      have hnat : (50037660898023895853 : ℕ)^512*5000000000000000^2071 ≤ 5000930855948461^2071*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037660898023895853 50000000000000000000 5000930855948461 5000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000930855948461/5000000000000000 : ℝ)) (X := (50037660898023895853/50000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6819181953572377/50000000000000000000 : ℝ) ≤ ((1317040784579786231/1317500000000000000 : ℝ)+2*(19790602223/10540000000000 : ℝ)*(11077/100000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (1317040784579786231/1317500000000000000 : ℝ)+2*(19790602223/10540000000000 : ℝ)*(11077/100000 : ℝ)=(5000337137881771/5000000000000000 : ℝ) by norm_num, show 1+2*(6819181953572377/50000000000000000000 : ℝ)=(25006819181953572377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37660898023895853/100000000000000000000 : ℝ)+(6819181953572377/50000000000000000000 : ℝ) ≤ ((1317040784579786231/1317500000000000000 : ℝ)+(19790602223/10540000000000 : ℝ)*((14239/100000 : ℝ)+(11077/100000 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (1317040784579786231/1317500000000000000 : ℝ)+(19790602223/10540000000000 : ℝ)*((14239/100000 : ℝ)+(11077/100000 : ℝ))=(1250158499228779/1250000000000000 : ℝ) by norm_num, show 1+(37660898023895853/100000000000000000000 : ℝ)+(6819181953572377/50000000000000000000 : ℝ)=(100051299261931040607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37660898023895853/100000000000000000000 : ℝ) ≤ ((1317040784579786231/1317500000000000000 : ℝ)+2*(19790602223/10540000000000 : ℝ)*(14239/100000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (1317040784579786231/1317500000000000000 : ℝ)+2*(19790602223/10540000000000 : ℝ)*(14239/100000 : ℝ)=(5000930855948461/5000000000000000 : ℝ) by norm_num, show 1+2*(37660898023895853/100000000000000000000 : ℝ)=(50037660898023895853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1317040784579786231/1317500000000000000 : ℝ)*(X 1 0+X 2 0)+(19790602223/10540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1317040784579786231/1317500000000000000 : ℝ)) (alpha := (19790602223/10540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1317040784579786231/1317500000000000000 : ℝ)*(X 0 1+X 2 1)+(19790602223/10540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1317040784579786231/1317500000000000000 : ℝ)) (alpha := (19790602223/10540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1317040784579786231/1317500000000000000 : ℝ)*(X 0 2+X 1 2)+(19790602223/10540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (11077/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1317040784579786231/1317500000000000000 : ℝ)) (alpha := (19790602223/10540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-273852833/1250000000 : ℝ)*X 0 0+(5396258857/10000000000 : ℝ)*X 0 1+(5262698507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336376009/2500000000 : ℝ)*X 1 0+(-2258616387/10000000000 : ℝ)*X 1 1+(5262696009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106910069/200000000 : ℝ)*X 2 0+(2631348861/5000000000 : ℝ)*X 2 1+(-2258614903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371647289/10000000000 : ℝ)*X 0 0+(4242083679/10000000000 : ℝ)*X 0 1+(2252598657/5000000000 : ℝ)*X 0 2+(4371647289/10000000000 : ℝ)*X 1 0+(4242083679/10000000000 : ℝ)*X 1 1+(2252598657/5000000000 : ℝ)*X 1 2+(4371647289/10000000000 : ℝ)*X 2 0+(4242083679/10000000000 : ℝ)*X 2 1+(2252598657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1095414221/5000000000 : ℝ)*X 0 0+(2631522169/5000000000 : ℝ)*X 0 1+(1079182311/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655896573/5000000000 : ℝ)*X 1 0+(-1062700791/5000000000 : ℝ)*X 1 1+(5395911557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327948291/2500000000 : ℝ)*X 2 0+(107918231/200000000 : ℝ)*X 2 1+(-2125401567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371658431/10000000000 : ℝ)*X 0 0+(563064337/1250000000 : ℝ)*X 0 1+(4242768631/10000000000 : ℝ)*X 0 2+(4371658431/10000000000 : ℝ)*X 1 0+(563064337/1250000000 : ℝ)*X 1 1+(4242768631/10000000000 : ℝ)*X 1 2+(4371658431/10000000000 : ℝ)*X 2 0+(563064337/1250000000 : ℝ)*X 2 1+(4242768631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10807569455299724520916449/32937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6720707/400000000000 : ℝ)*(base19) + (1098225951/100000000000000 : ℝ)*(base23) + (49954037/50000000000000 : ℝ)*(lower2) + (44750531/20000000000000 : ℝ)*(lower3) + (2821980161710469/50000000000000 : ℝ)*(major0) + (2821980161710469/50000000000000 : ℝ)*(major1) + (2821980161710469/50000000000000 : ℝ)*(major2) + (1871811738798123/25000000000000 : ℝ)*(sp0) + (748718142279703/10000000000000 : ℝ)*(sp1) + (7487249513751487/100000000000000 : ℝ)*(sp2) + (29692635258899/781250000000 : ℝ)*(sp3) + (1828392473/50000000000000 : ℝ)*(sp4) + (33754501829/50000000000000 : ℝ)*(sp5) + (6355393951/50000000000000 : ℝ)*(sp7) + (1900335011963487/50000000000000 : ℝ)*(f.failure) + (7487250611977439/100000000000000 : ℝ)*(f.sum) + (316692189519/131750000000000000000000000 : ℝ)*base66 + (417465374040127339/65875000000000000000000000000000 : ℝ)*base67 + (814252621709627339/65875000000000000000000000000000 : ℝ)*base69 + (356631942859877339/65875000000000000000000000000000 : ℝ)*base71 + (111274261637/65875000000000000000000000 : ℝ)*base73 + (1253107372315377339/65875000000000000000000000000000 : ℝ)*base75 + (1274007917353127339/65875000000000000000000000000000 : ℝ)*base77 + (688529456290877339/65875000000000000000000000000000 : ℝ)*base79 + (2255309652431/527000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (549991/312500000000000000000 : ℝ)*base89 + (549991/312500000000000000000 : ℝ)*base91 + (549991/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2842420791776499611067/263500000000000000000000000 : ℝ) := by norm_num
    linear_combination (403760607/20000000000000 : ℝ)*(base19) + (2243308533/100000000000000 : ℝ)*(base23) + (11822889/5000000000000 : ℝ)*(upper3) + (21220201/25000000000000 : ℝ)*(lower4) + (8670353/4000000000000 : ℝ)*(upper5) + (5673402680008347/100000000000000 : ℝ)*(major0) + (5673402680008347/100000000000000 : ℝ)*(major1) + (5673402680008347/100000000000000 : ℝ)*(major2) + (6516903113/12500000000000 : ℝ)*(sp1) + (58313656161/100000000000000 : ℝ)*(sp2) + (1881577088000303/25000000000000 : ℝ)*(sp4) + (7526254197973273/100000000000000 : ℝ)*(sp5) + (7526247795036517/100000000000000 : ℝ)*(sp6) + (76409932968859/2000000000000 : ℝ)*(sp7) + (76409932968859/2000000000000 : ℝ)*(f.failure) + (1881577088000303/25000000000000 : ℝ)*(f.sum) + (1319265490761/527000000000000000000000000 : ℝ)*base66 + (1258900609299704843/131750000000000000000000000000000 : ℝ)*base68 + (652149575985795157/131750000000000000000000000000000 : ℝ)*base69 + (1979043473772704843/131750000000000000000000000000000 : ℝ)*base72 + (21703861201/527000000000000000000000000 : ℝ)*base74 + (2871976401986045157/131750000000000000000000000000000 : ℝ)*base75 + (1425649797334295157/131750000000000000000000000000000 : ℝ)*base77 + (1911365994117704843/131750000000000000000000000000000 : ℝ)*base80 + (32212817227/21080000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6213/12500000000000000000 : ℝ)*base90 + (6213/12500000000000000000 : ℝ)*base92 + (6213/12500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1092_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1092_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1092_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1092_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1092_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1092_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
