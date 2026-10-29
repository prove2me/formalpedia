-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:37.367808+00:00
-- url     : https://prove2.me/submissions/75ce331d-c14e-423d-9e73-7cfca113746f

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
theorem support_rectangle_w1667_s0_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182910919/1250000000 : ℝ)*x 0 + (5764629889/10000000000 : ℝ)*x 1 + (986573169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182910919/1250000000 : ℝ)^4987 ≤ (8905515182677/100000000000000 : ℝ)^3963 := by
    have hnat : (182910919 : ℕ)^4987*100000000000000^3963 ≤ 8905515182677^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182910919 1250000000 8905515182677 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5764629889/10000000000 : ℝ)^4987 ≤ (6249814766587/12500000000000 : ℝ)^3963 := by
    have hnat : (5764629889 : ℕ)^4987*12500000000000^3963 ≤ 6249814766587^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764629889 10000000000 6249814766587 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986573169/2000000000 : ℝ)^4987 ≤ (821919333353/2000000000000 : ℝ)^3963 := by
    have hnat : (986573169 : ℕ)^4987*2000000000000^3963 ≤ 821919333353^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986573169 2000000000 821919333353 2000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182910919/1250000000 : ℝ), (5764629889/10000000000 : ℝ), (986573169/2000000000 : ℝ)] ![(8905515182677/100000000000000 : ℝ), (6249814766587/12500000000000 : ℝ), (821919333353/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182910919/1250000000 : ℝ)|^4987 ≤ (8905515182677/100000000000000 : ℝ)^3963
        have hw : |(-182910919/1250000000 : ℝ)|=(182910919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5764629889/10000000000 : ℝ)|^4987 ≤ (6249814766587/12500000000000 : ℝ)^3963
        have hw : |(5764629889/10000000000 : ℝ)|=(5764629889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(986573169/2000000000 : ℝ)|^4987 ≤ (821919333353/2000000000000 : ℝ)^3963
        have hw : |(986573169/2000000000 : ℝ)|=(986573169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086171183/2000000000 : ℝ)*x 0 + (-119894423/625000000 : ℝ)*x 1 + (2466433369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086171183/2000000000 : ℝ)^4987 ≤ (9276643407651/20000000000000 : ℝ)^3963 := by
    have hnat : (1086171183 : ℕ)^4987*20000000000000^3963 ≤ 9276643407651^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086171183 2000000000 9276643407651 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119894423/625000000 : ℝ)^4987 ≤ (12520806908931/100000000000000 : ℝ)^3963 := by
    have hnat : (119894423 : ℕ)^4987*100000000000000^3963 ≤ 12520806908931^3963*625000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119894423 625000000 12520806908931 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2466433369/5000000000 : ℝ)^4987 ≤ (41095976029607/100000000000000 : ℝ)^3963 := by
    have hnat : (2466433369 : ℕ)^4987*100000000000000^3963 ≤ 41095976029607^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466433369 5000000000 41095976029607 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086171183/2000000000 : ℝ), (-119894423/625000000 : ℝ), (2466433369/5000000000 : ℝ)] ![(9276643407651/20000000000000 : ℝ), (12520806908931/100000000000000 : ℝ), (41095976029607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086171183/2000000000 : ℝ)|^4987 ≤ (9276643407651/20000000000000 : ℝ)^3963
        have hw : |(1086171183/2000000000 : ℝ)|=(1086171183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119894423/625000000 : ℝ)|^4987 ≤ (12520806908931/100000000000000 : ℝ)^3963
        have hw : |(-119894423/625000000 : ℝ)|=(119894423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2466433369/5000000000 : ℝ)|^4987 ≤ (41095976029607/100000000000000 : ℝ)^3963
        have hw : |(2466433369/5000000000 : ℝ)|=(2466433369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5430857927/10000000000 : ℝ)*x 0 + (1233216369/2500000000 : ℝ)*x 1 + (-1918309747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5430857927/10000000000 : ℝ)^4987 ≤ (5797904832781/12500000000000 : ℝ)^3963 := by
    have hnat : (5430857927 : ℕ)^4987*12500000000000^3963 ≤ 5797904832781^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430857927 10000000000 5797904832781 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233216369/2500000000 : ℝ)^4987 ≤ (41095962799159/100000000000000 : ℝ)^3963 := by
    have hnat : (1233216369 : ℕ)^4987*100000000000000^3963 ≤ 41095962799159^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233216369 2500000000 41095962799159 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918309747/10000000000 : ℝ)^4987 ≤ (626039926147/5000000000000 : ℝ)^3963 := by
    have hnat : (1918309747 : ℕ)^4987*5000000000000^3963 ≤ 626039926147^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918309747 10000000000 626039926147 5000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5430857927/10000000000 : ℝ), (1233216369/2500000000 : ℝ), (-1918309747/10000000000 : ℝ)] ![(5797904832781/12500000000000 : ℝ), (41095962799159/100000000000000 : ℝ), (626039926147/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5430857927/10000000000 : ℝ)|^4987 ≤ (5797904832781/12500000000000 : ℝ)^3963
        have hw : |(5430857927/10000000000 : ℝ)|=(5430857927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1233216369/2500000000 : ℝ)|^4987 ≤ (41095962799159/100000000000000 : ℝ)^3963
        have hw : |(1233216369/2500000000 : ℝ)|=(1233216369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918309747/10000000000 : ℝ)|^4987 ≤ (626039926147/5000000000000 : ℝ)^3963
        have hw : |(-1918309747/10000000000 : ℝ)|=(1918309747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20413647/50000000 : ℝ)*x 0 + (1543550761/5000000000 : ℝ)*x 1 + (660654923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20413647/50000000 : ℝ)^4987 ≤ (16195489649153/50000000000000 : ℝ)^3963 := by
    have hnat : (20413647 : ℕ)^4987*50000000000000^3963 ≤ 16195489649153^3963*50000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20413647 50000000 16195489649153 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543550761/5000000000 : ℝ)^4987 ≤ (11392680575483/50000000000000 : ℝ)^3963 := by
    have hnat : (1543550761 : ℕ)^4987*50000000000000^3963 ≤ 11392680575483^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543550761 5000000000 11392680575483 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660654923/1250000000 : ℝ)^4987 ≤ (44823659529769/100000000000000 : ℝ)^3963 := by
    have hnat : (660654923 : ℕ)^4987*100000000000000^3963 ≤ 44823659529769^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660654923 1250000000 44823659529769 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20413647/50000000 : ℝ), (1543550761/5000000000 : ℝ), (660654923/1250000000 : ℝ)] ![(16195489649153/50000000000000 : ℝ), (11392680575483/50000000000000 : ℝ), (44823659529769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20413647/50000000 : ℝ)|^4987 ≤ (16195489649153/50000000000000 : ℝ)^3963
        have hw : |(20413647/50000000 : ℝ)|=(20413647/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1543550761/5000000000 : ℝ)|^4987 ≤ (11392680575483/50000000000000 : ℝ)^3963
        have hw : |(1543550761/5000000000 : ℝ)|=(1543550761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660654923/1250000000 : ℝ)|^4987 ≤ (44823659529769/100000000000000 : ℝ)^3963
        have hw : |(660654923/1250000000 : ℝ)|=(660654923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1465399809/10000000000 : ℝ)*x 0 + (2476653627/5000000000 : ℝ)*x 1 + (574349207/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1465399809/10000000000 : ℝ)^4987 ≤ (4460848244271/50000000000000 : ℝ)^3963 := by
    have hnat : (1465399809 : ℕ)^4987*50000000000000^3963 ≤ 4460848244271^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465399809 10000000000 4460848244271 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2476653627/5000000000 : ℝ)^4987 ≤ (41310383181149/100000000000000 : ℝ)^3963 := by
    have hnat : (2476653627 : ℕ)^4987*100000000000000^3963 ≤ 41310383181149^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476653627 5000000000 41310383181149 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574349207/1000000000 : ℝ)^4987 ≤ (2488396015601/5000000000000 : ℝ)^3963 := by
    have hnat : (574349207 : ℕ)^4987*5000000000000^3963 ≤ 2488396015601^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574349207 1000000000 2488396015601 5000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1465399809/10000000000 : ℝ), (2476653627/5000000000 : ℝ), (574349207/1000000000 : ℝ)] ![(4460848244271/50000000000000 : ℝ), (41310383181149/100000000000000 : ℝ), (2488396015601/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1465399809/10000000000 : ℝ)|^4987 ≤ (4460848244271/50000000000000 : ℝ)^3963
        have hw : |(-1465399809/10000000000 : ℝ)|=(1465399809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2476653627/5000000000 : ℝ)|^4987 ≤ (41310383181149/100000000000000 : ℝ)^3963
        have hw : |(2476653627/5000000000 : ℝ)|=(2476653627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(574349207/1000000000 : ℝ)|^4987 ≤ (2488396015601/5000000000000 : ℝ)^3963
        have hw : |(574349207/1000000000 : ℝ)|=(574349207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204027309/10000000000 : ℝ)*x 0 + (-553842279/5000000000 : ℝ)*x 1 + (1148698723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204027309/10000000000 : ℝ)^4987 ≤ (21979333622343/50000000000000 : ℝ)^3963 := by
    have hnat : (5204027309 : ℕ)^4987*50000000000000^3963 ≤ 21979333622343^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204027309 10000000000 21979333622343 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553842279/5000000000 : ℝ)^4987 ≤ (784174448373/12500000000000 : ℝ)^3963 := by
    have hnat : (553842279 : ℕ)^4987*12500000000000^3963 ≤ 784174448373^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553842279 5000000000 784174448373 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148698723/2000000000 : ℝ)^4987 ≤ (24883968579407/50000000000000 : ℝ)^3963 := by
    have hnat : (1148698723 : ℕ)^4987*50000000000000^3963 ≤ 24883968579407^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148698723 2000000000 24883968579407 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204027309/10000000000 : ℝ), (-553842279/5000000000 : ℝ), (1148698723/2000000000 : ℝ)] ![(21979333622343/50000000000000 : ℝ), (784174448373/12500000000000 : ℝ), (24883968579407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204027309/10000000000 : ℝ)|^4987 ≤ (21979333622343/50000000000000 : ℝ)^3963
        have hw : |(5204027309/10000000000 : ℝ)|=(5204027309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553842279/5000000000 : ℝ)|^4987 ≤ (784174448373/12500000000000 : ℝ)^3963
        have hw : |(-553842279/5000000000 : ℝ)|=(553842279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1148698723/2000000000 : ℝ)|^4987 ≤ (24883968579407/50000000000000 : ℝ)^3963
        have hw : |(1148698723/2000000000 : ℝ)|=(1148698723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204027633/10000000000 : ℝ)*x 0 + (5743493167/10000000000 : ℝ)*x 1 + (-1107684759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204027633/10000000000 : ℝ)^4987 ≤ (43958670688703/100000000000000 : ℝ)^3963 := by
    have hnat : (5204027633 : ℕ)^4987*100000000000000^3963 ≤ 43958670688703^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204027633 10000000000 43958670688703 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5743493167/10000000000 : ℝ)^4987 ≤ (49767932273789/100000000000000 : ℝ)^3963 := by
    have hnat : (5743493167 : ℕ)^4987*100000000000000^3963 ≤ 49767932273789^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5743493167 10000000000 49767932273789 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107684759/10000000000 : ℝ)^4987 ≤ (1254679403899/20000000000000 : ℝ)^3963 := by
    have hnat : (1107684759 : ℕ)^4987*20000000000000^3963 ≤ 1254679403899^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107684759 10000000000 1254679403899 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204027633/10000000000 : ℝ), (5743493167/10000000000 : ℝ), (-1107684759/10000000000 : ℝ)] ![(43958670688703/100000000000000 : ℝ), (49767932273789/100000000000000 : ℝ), (1254679403899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204027633/10000000000 : ℝ)|^4987 ≤ (43958670688703/100000000000000 : ℝ)^3963
        have hw : |(5204027633/10000000000 : ℝ)|=(5204027633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5743493167/10000000000 : ℝ)|^4987 ≤ (49767932273789/100000000000000 : ℝ)^3963
        have hw : |(5743493167/10000000000 : ℝ)|=(5743493167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1107684759/10000000000 : ℝ)|^4987 ≤ (1254679403899/20000000000000 : ℝ)^3963
        have hw : |(-1107684759/10000000000 : ℝ)|=(1107684759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s0_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511038911/1250000000 : ℝ)*x 0 + (5231217661/10000000000 : ℝ)*x 1 + (3142961777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511038911/1250000000 : ℝ)^4987 ≤ (32446716681503/100000000000000 : ℝ)^3963 := by
    have hnat : (511038911 : ℕ)^4987*100000000000000^3963 ≤ 32446716681503^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511038911 1250000000 32446716681503 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231217661/10000000000 : ℝ)^4987 ≤ (44247886870417/100000000000000 : ℝ)^3963 := by
    have hnat : (5231217661 : ℕ)^4987*100000000000000^3963 ≤ 44247886870417^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231217661 10000000000 44247886870417 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3142961777/10000000000 : ℝ)^4987 ≤ (23305396428383/100000000000000 : ℝ)^3963 := by
    have hnat : (3142961777 : ℕ)^4987*100000000000000^3963 ≤ 23305396428383^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142961777 10000000000 23305396428383 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511038911/1250000000 : ℝ), (5231217661/10000000000 : ℝ), (3142961777/10000000000 : ℝ)] ![(32446716681503/100000000000000 : ℝ), (44247886870417/100000000000000 : ℝ), (23305396428383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511038911/1250000000 : ℝ)|^4987 ≤ (32446716681503/100000000000000 : ℝ)^3963
        have hw : |(511038911/1250000000 : ℝ)|=(511038911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231217661/10000000000 : ℝ)|^4987 ≤ (44247886870417/100000000000000 : ℝ)^3963
        have hw : |(5231217661/10000000000 : ℝ)|=(5231217661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3142961777/10000000000 : ℝ)|^4987 ≤ (23305396428383/100000000000000 : ℝ)^3963
        have hw : |(3142961777/10000000000 : ℝ)|=(3142961777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1033/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23001/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4983/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4983 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4983*1^1024 ≤ 0^1024*1^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4983/1024 : ℝ) ≤ (231510116223284407/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4983 ≤ (231510116223284407/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4983*20000000000000000000^1024 ≤ 231510116223284407^1024*5^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 231510116223284407 20000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (231510116223284407/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4983 := by
      have hnat : (1 : ℕ)^1024*1^4983 ≤ 1^4983*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20231510116223284407/20000000000000000000 : ℝ) ≤ (5011839440399569/5000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (20231510116223284407/20000000000000000000 : ℝ)^1024 ≤ (5011839440399569/5000000000000000 : ℝ)^4983 := by
      have hnat : (20231510116223284407 : ℕ)^1024*5000000000000000^4983 ≤ 5011839440399569^4983*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20231510116223284407 20000000000000000000 5011839440399569 5000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011839440399569/5000000000000000 : ℝ)) (X := (20231510116223284407/20000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10231510116223284407/10000000000000000000 : ℝ) ≤ (2511839440399569/2500000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (10231510116223284407/10000000000000000000 : ℝ)^1024 ≤ (2511839440399569/2500000000000000 : ℝ)^4983 := by
      have hnat : (10231510116223284407 : ℕ)^1024*2500000000000000^4983 ≤ 2511839440399569^4983*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10231510116223284407 10000000000000000000 2511839440399569 2500000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511839440399569/2500000000000000 : ℝ)) (X := (10231510116223284407/10000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11839440399569/2000000000000000 : ℝ)*(0 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11839440399569/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231510116223284407/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11839440399569/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11839440399569/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5011839440399569/5000000000000000 : ℝ) by norm_num, show 1+(231510116223284407/20000000000000000000 : ℝ)+(0 : ℝ)=(20231510116223284407/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231510116223284407/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11839440399569/2000000000000000 : ℝ)*(2/5 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11839440399569/2000000000000000 : ℝ)*(2/5 : ℝ)=(2511839440399569/2500000000000000 : ℝ) by norm_num, show 1+2*(231510116223284407/20000000000000000000 : ℝ)=(10231510116223284407/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11839440399569/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11839440399569/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11839440399569/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11839440399569/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11839440399569/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11839440399569/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-182910919/1250000000 : ℝ)*X 0 0+(5764629889/10000000000 : ℝ)*X 0 1+(986573169/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1086171183/2000000000 : ℝ)*X 1 0+(-119894423/625000000 : ℝ)*X 1 1+(2466433369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5430857927/10000000000 : ℝ)*X 2 0+(1233216369/2500000000 : ℝ)*X 2 1+(-1918309747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20413647/50000000 : ℝ)*X 0 0+(1543550761/5000000000 : ℝ)*X 0 1+(660654923/1250000000 : ℝ)*X 0 2+(20413647/50000000 : ℝ)*X 1 0+(1543550761/5000000000 : ℝ)*X 1 1+(660654923/1250000000 : ℝ)*X 1 2+(20413647/50000000 : ℝ)*X 2 0+(1543550761/5000000000 : ℝ)*X 2 1+(660654923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1465399809/10000000000 : ℝ)*X 0 0+(2476653627/5000000000 : ℝ)*X 0 1+(574349207/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5204027309/10000000000 : ℝ)*X 1 0+(-553842279/5000000000 : ℝ)*X 1 1+(1148698723/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204027633/10000000000 : ℝ)*X 2 0+(5743493167/10000000000 : ℝ)*X 2 1+(-1107684759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511038911/1250000000 : ℝ)*X 0 0+(5231217661/10000000000 : ℝ)*X 0 1+(3142961777/10000000000 : ℝ)*X 0 2+(511038911/1250000000 : ℝ)*X 1 0+(5231217661/10000000000 : ℝ)*X 1 1+(3142961777/10000000000 : ℝ)*X 1 2+(511038911/1250000000 : ℝ)*X 2 0+(5231217661/10000000000 : ℝ)*X 2 1+(3142961777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (324541426052154687908739/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29209781/20000000000000 : ℝ)*(base1) + (1095857327/100000000000000 : ℝ)*(base19) + (739477569/50000000000000 : ℝ)*(base23) + (62315289/100000000000000 : ℝ)*(base24) + (262559097/100000000000000 : ℝ)*(upper5) + (828605206934341/100000000000000 : ℝ)*(major0) + (828605206934341/100000000000000 : ℝ)*(major1) + (828605206934341/100000000000000 : ℝ)*(major2) + (300566986299629/25000000000000 : ℝ)*(sp0) + (1202273989075699/100000000000000 : ℝ)*(sp1) + (1202273543662599/100000000000000 : ℝ)*(sp2) + (113733239584347/25000000000000 : ℝ)*(sp3) + (1457156683/20000000000000 : ℝ)*(sp4) + (1004094203/50000000000000 : ℝ)*(sp7) + (4549351125747/1000000000000 : ℝ)*(f.failure) + (601137542466513/50000000000000 : ℝ)*(f.sum) + (124238911599029/100000000000000000000000000000 : ℝ)*base65 + (1841862580499029/200000000000000000000000000000 : ℝ)*base67 + (387948282899029/200000000000000000000000000000 : ℝ)*base69 + (1051289845099029/200000000000000000000000000000 : ℝ)*base71 + (527326980699029/100000000000000000000000000000 : ℝ)*base73 + (17929324499029/200000000000000000000000000000 : ℝ)*base75 + (832157307499029/200000000000000000000000000000 : ℝ)*base77 + (1194843582499029/200000000000000000000000000000 : ℝ)*base79 + (513259187599029/100000000000000000000000000000 : ℝ)*base81 + (470723/100000000000000000000 : ℝ)*base89 + (470723/100000000000000000000 : ℝ)*base91 + (470723/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100744276523578857131031/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4481059/4000000000000 : ℝ)*(base19) + (50735869/25000000000000 : ℝ)*(base23) + (15000323/25000000000000 : ℝ)*(base32) + (157724477/100000000000000 : ℝ)*(upper3) + (5389889/20000000000000 : ℝ)*(upper5) + (436098595629133/50000000000000 : ℝ)*(major0) + (436098595629133/50000000000000 : ℝ)*(major1) + (436098595629133/50000000000000 : ℝ)*(major2) + (1054534073/100000000000000 : ℝ)*(sp1) + (1332726861/100000000000000 : ℝ)*(sp2) + (632762790096369/50000000000000 : ℝ)*(sp4) + (126552441363219/10000000000000 : ℝ)*(sp5) + (1265524044522401/100000000000000 : ℝ)*(sp6) + (478868675159647/100000000000000 : ℝ)*(sp7) + (478868735160939/100000000000000 : ℝ)*(f.failure) + (632762790096369/50000000000000 : ℝ)*(f.sum) + (17027957656323/50000000000000000000000000000 : ℝ)*base66 + (138717745143677/100000000000000000000000000000 : ℝ)*base67 + (104677580856323/100000000000000000000000000000 : ℝ)*base70 + (202686072943677/100000000000000000000000000000 : ℝ)*base71 + (56207822106323/50000000000000000000000000000 : ℝ)*base74 + (371498112743677/100000000000000000000000000000 : ℝ)*base75 + (391024525443677/100000000000000000000000000000 : ℝ)*base77 + (375401410043677/100000000000000000000000000000 : ℝ)*base79 + (204188152606323/50000000000000000000000000000 : ℝ)*base82 + (36908549/10000000000000000000000 : ℝ)*base90 + (36908549/10000000000000000000000 : ℝ)*base92 + (36908549/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1667_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1033/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1667_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1667_s1_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-312466383/2000000000 : ℝ)*x 0 + (6855101/12500000 : ℝ)*x 1 + (514889667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312466383/2000000000 : ℝ)^4987 ≤ (2417643770991/25000000000000 : ℝ)^3963 := by
    have hnat : (312466383 : ℕ)^4987*25000000000000^3963 ≤ 2417643770991^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312466383 2000000000 2417643770991 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6855101/12500000 : ℝ)^4987 ≤ (46955974600861/100000000000000 : ℝ)^3963 := by
    have hnat : (6855101 : ℕ)^4987*100000000000000^3963 ≤ 46955974600861^3963*12500000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6855101 12500000 46955974600861 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514889667/1000000000 : ℝ)^4987 ≤ (43373450300239/100000000000000 : ℝ)^3963 := by
    have hnat : (514889667 : ℕ)^4987*100000000000000^3963 ≤ 43373450300239^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514889667 1000000000 43373450300239 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-312466383/2000000000 : ℝ), (6855101/12500000 : ℝ), (514889667/1000000000 : ℝ)] ![(2417643770991/25000000000000 : ℝ), (46955974600861/100000000000000 : ℝ), (43373450300239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-312466383/2000000000 : ℝ)|^4987 ≤ (2417643770991/25000000000000 : ℝ)^3963
        have hw : |(-312466383/2000000000 : ℝ)|=(312466383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6855101/12500000 : ℝ)|^4987 ≤ (46955974600861/100000000000000 : ℝ)^3963
        have hw : |(6855101/12500000 : ℝ)|=(6855101/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514889667/1000000000 : ℝ)|^4987 ≤ (43373450300239/100000000000000 : ℝ)^3963
        have hw : |(514889667/1000000000 : ℝ)|=(514889667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356224701/10000000000 : ℝ)*x 0 + (-868110801/5000000000 : ℝ)*x 1 + (5148896397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356224701/10000000000 : ℝ)^4987 ≤ (22791273097767/50000000000000 : ℝ)^3963 := by
    have hnat : (5356224701 : ℕ)^4987*50000000000000^3963 ≤ 22791273097767^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356224701 10000000000 22791273097767 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868110801/5000000000 : ℝ)^4987 ≤ (5522003191721/50000000000000 : ℝ)^3963 := by
    have hnat : (868110801 : ℕ)^4987*50000000000000^3963 ≤ 5522003191721^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868110801 5000000000 5522003191721 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148896397/10000000000 : ℝ)^4987 ≤ (43373447406311/100000000000000 : ℝ)^3963 := by
    have hnat : (5148896397 : ℕ)^4987*100000000000000^3963 ≤ 43373447406311^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148896397 10000000000 43373447406311 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356224701/10000000000 : ℝ), (-868110801/5000000000 : ℝ), (5148896397/10000000000 : ℝ)] ![(22791273097767/50000000000000 : ℝ), (5522003191721/50000000000000 : ℝ), (43373447406311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356224701/10000000000 : ℝ)|^4987 ≤ (22791273097767/50000000000000 : ℝ)^3963
        have hw : |(5356224701/10000000000 : ℝ)|=(5356224701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868110801/5000000000 : ℝ)|^4987 ≤ (5522003191721/50000000000000 : ℝ)^3963
        have hw : |(-868110801/5000000000 : ℝ)|=(868110801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148896397/10000000000 : ℝ)|^4987 ≤ (43373447406311/100000000000000 : ℝ)^3963
        have hw : |(5148896397/10000000000 : ℝ)|=(5148896397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678112069/5000000000 : ℝ)*x 0 + (257444851/500000000 : ℝ)*x 1 + (-1736221531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678112069/5000000000 : ℝ)^4987 ≤ (22791270083141/50000000000000 : ℝ)^3963 := by
    have hnat : (2678112069 : ℕ)^4987*50000000000000^3963 ≤ 22791270083141^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678112069 5000000000 22791270083141 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257444851/500000000 : ℝ)^4987 ≤ (43373454010403/100000000000000 : ℝ)^3963 := by
    have hnat : (257444851 : ℕ)^4987*100000000000000^3963 ≤ 43373454010403^3963*500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257444851 500000000 43373454010403 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736221531/10000000000 : ℝ)^4987 ≤ (11044005815119/100000000000000 : ℝ)^3963 := by
    have hnat : (1736221531 : ℕ)^4987*100000000000000^3963 ≤ 11044005815119^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736221531 10000000000 11044005815119 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678112069/5000000000 : ℝ), (257444851/500000000 : ℝ), (-1736221531/10000000000 : ℝ)] ![(22791270083141/50000000000000 : ℝ), (43373454010403/100000000000000 : ℝ), (11044005815119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678112069/5000000000 : ℝ)|^4987 ≤ (22791270083141/50000000000000 : ℝ)^3963
        have hw : |(2678112069/5000000000 : ℝ)|=(2678112069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257444851/500000000 : ℝ)|^4987 ≤ (43373454010403/100000000000000 : ℝ)^3963
        have hw : |(257444851/500000000 : ℝ)|=(257444851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736221531/10000000000 : ℝ)|^4987 ≤ (11044005815119/100000000000000 : ℝ)^3963
        have hw : |(-1736221531/10000000000 : ℝ)|=(1736221531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416169317/1000000000 : ℝ)*x 0 + (233464671/625000000 : ℝ)*x 1 + (4621239911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416169317/1000000000 : ℝ)^4987 ≤ (16590642723947/50000000000000 : ℝ)^3963 := by
    have hnat : (416169317 : ℕ)^4987*50000000000000^3963 ≤ 16590642723947^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416169317 1000000000 16590642723947 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233464671/625000000 : ℝ)^4987 ≤ (7240663184607/25000000000000 : ℝ)^3963 := by
    have hnat : (233464671 : ℕ)^4987*25000000000000^3963 ≤ 7240663184607^3963*625000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233464671 625000000 7240663184607 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4621239911/10000000000 : ℝ)^4987 ≤ (3785606179429/10000000000000 : ℝ)^3963 := by
    have hnat : (4621239911 : ℕ)^4987*10000000000000^3963 ≤ 3785606179429^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4621239911 10000000000 3785606179429 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416169317/1000000000 : ℝ), (233464671/625000000 : ℝ), (4621239911/10000000000 : ℝ)] ![(16590642723947/50000000000000 : ℝ), (7240663184607/25000000000000 : ℝ), (3785606179429/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416169317/1000000000 : ℝ)|^4987 ≤ (16590642723947/50000000000000 : ℝ)^3963
        have hw : |(416169317/1000000000 : ℝ)|=(416169317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233464671/625000000 : ℝ)|^4987 ≤ (7240663184607/25000000000000 : ℝ)^3963
        have hw : |(233464671/625000000 : ℝ)|=(233464671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4621239911/10000000000 : ℝ)|^4987 ≤ (3785606179429/10000000000000 : ℝ)^3963
        have hw : |(4621239911/10000000000 : ℝ)|=(4621239911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-781233807/5000000000 : ℝ)*x 0 + (257610591/500000000 : ℝ)*x 1 + (5480720597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (781233807/5000000000 : ℝ)^4987 ≤ (4835816042987/50000000000000 : ℝ)^3963 := by
    have hnat : (781233807 : ℕ)^4987*50000000000000^3963 ≤ 4835816042987^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781233807 5000000000 4835816042987 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257610591/500000000 : ℝ)^4987 ≤ (10852148842161/25000000000000 : ℝ)^3963 := by
    have hnat : (257610591 : ℕ)^4987*25000000000000^3963 ≤ 10852148842161^3963*500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257610591 500000000 10852148842161 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480720597/10000000000 : ℝ)^4987 ≤ (23459886263929/50000000000000 : ℝ)^3963 := by
    have hnat : (5480720597 : ℕ)^4987*50000000000000^3963 ≤ 23459886263929^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480720597 10000000000 23459886263929 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-781233807/5000000000 : ℝ), (257610591/500000000 : ℝ), (5480720597/10000000000 : ℝ)] ![(4835816042987/50000000000000 : ℝ), (10852148842161/25000000000000 : ℝ), (23459886263929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-781233807/5000000000 : ℝ)|^4987 ≤ (4835816042987/50000000000000 : ℝ)^3963
        have hw : |(-781233807/5000000000 : ℝ)|=(781233807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257610591/500000000 : ℝ)|^4987 ≤ (10852148842161/25000000000000 : ℝ)^3963
        have hw : |(257610591/500000000 : ℝ)|=(257610591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480720597/10000000000 : ℝ)|^4987 ≤ (23459886263929/50000000000000 : ℝ)^3963
        have hw : |(5480720597/10000000000 : ℝ)|=(5480720597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316615389/2500000000 : ℝ)*x 0 + (-1404397979/10000000000 : ℝ)*x 1 + (685090073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316615389/2500000000 : ℝ)^4987 ≤ (11155837255487/25000000000000 : ℝ)^3963 := by
    have hnat : (1316615389 : ℕ)^4987*25000000000000^3963 ≤ 11155837255487^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316615389 2500000000 11155837255487 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404397979/10000000000 : ℝ)^4987 ≤ (2114219643957/25000000000000 : ℝ)^3963 := by
    have hnat : (1404397979 : ℕ)^4987*25000000000000^3963 ≤ 2114219643957^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404397979 10000000000 2114219643957 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685090073/1250000000 : ℝ)^4987 ≤ (4691977238781/10000000000000 : ℝ)^3963 := by
    have hnat : (685090073 : ℕ)^4987*10000000000000^3963 ≤ 4691977238781^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685090073 1250000000 4691977238781 10000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316615389/2500000000 : ℝ), (-1404397979/10000000000 : ℝ), (685090073/1250000000 : ℝ)] ![(11155837255487/25000000000000 : ℝ), (2114219643957/25000000000000 : ℝ), (4691977238781/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316615389/2500000000 : ℝ)|^4987 ≤ (11155837255487/25000000000000 : ℝ)^3963
        have hw : |(1316615389/2500000000 : ℝ)|=(1316615389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404397979/10000000000 : ℝ)|^4987 ≤ (2114219643957/25000000000000 : ℝ)^3963
        have hw : |(-1404397979/10000000000 : ℝ)|=(1404397979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685090073/1250000000 : ℝ)|^4987 ≤ (4691977238781/10000000000000 : ℝ)^3963
        have hw : |(685090073/1250000000 : ℝ)|=(685090073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316615387/2500000000 : ℝ)*x 0 + (5480720593/10000000000 : ℝ)*x 1 + (-702198989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316615387/2500000000 : ℝ)^4987 ≤ (5577918617081/12500000000000 : ℝ)^3963 := by
    have hnat : (1316615387 : ℕ)^4987*12500000000000^3963 ≤ 5577918617081^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316615387 2500000000 5577918617081 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480720593/10000000000 : ℝ)^4987 ≤ (23459886242383/50000000000000 : ℝ)^3963 := by
    have hnat : (5480720593 : ℕ)^4987*50000000000000^3963 ≤ 23459886242383^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480720593 10000000000 23459886242383 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702198989/5000000000 : ℝ)^4987 ≤ (8456878568251/100000000000000 : ℝ)^3963 := by
    have hnat : (702198989 : ℕ)^4987*100000000000000^3963 ≤ 8456878568251^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702198989 5000000000 8456878568251 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316615387/2500000000 : ℝ), (5480720593/10000000000 : ℝ), (-702198989/5000000000 : ℝ)] ![(5577918617081/12500000000000 : ℝ), (23459886242383/50000000000000 : ℝ), (8456878568251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316615387/2500000000 : ℝ)|^4987 ≤ (5577918617081/12500000000000 : ℝ)^3963
        have hw : |(1316615387/2500000000 : ℝ)|=(1316615387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480720593/10000000000 : ℝ)|^4987 ≤ (23459886242383/50000000000000 : ℝ)^3963
        have hw : |(5480720593/10000000000 : ℝ)|=(5480720593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-702198989/5000000000 : ℝ)|^4987 ≤ (8456878568251/100000000000000 : ℝ)^3963
        have hw : |(-702198989/5000000000 : ℝ)|=(702198989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s1_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162052823/10000000000 : ℝ)*x 0 + (4612479167/10000000000 : ℝ)*x 1 + (748863169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162052823/10000000000 : ℝ)^4987 ≤ (8296223487537/25000000000000 : ℝ)^3963 := by
    have hnat : (4162052823 : ℕ)^4987*25000000000000^3963 ≤ 8296223487537^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162052823 10000000000 8296223487537 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612479167/10000000000 : ℝ)^4987 ≤ (37765774472457/100000000000000 : ℝ)^3963 := by
    have hnat : (4612479167 : ℕ)^4987*100000000000000^3963 ≤ 37765774472457^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612479167 10000000000 37765774472457 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748863169/2000000000 : ℝ)^4987 ≤ (14524665778337/50000000000000 : ℝ)^3963 := by
    have hnat : (748863169 : ℕ)^4987*50000000000000^3963 ≤ 14524665778337^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748863169 2000000000 14524665778337 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162052823/10000000000 : ℝ), (4612479167/10000000000 : ℝ), (748863169/2000000000 : ℝ)] ![(8296223487537/25000000000000 : ℝ), (37765774472457/100000000000000 : ℝ), (14524665778337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162052823/10000000000 : ℝ)|^4987 ≤ (8296223487537/25000000000000 : ℝ)^3963
        have hw : |(4162052823/10000000000 : ℝ)|=(4162052823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4612479167/10000000000 : ℝ)|^4987 ≤ (37765774472457/100000000000000 : ℝ)^3963
        have hw : |(4612479167/10000000000 : ℝ)|=(4612479167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748863169/2000000000 : ℝ)|^4987 ≤ (14524665778337/50000000000000 : ℝ)^3963
        have hw : |(748863169/2000000000 : ℝ)|=(748863169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (399/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3421/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1033/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1033/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1033/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1033/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1033/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1033/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1033/20000 : ℝ) ^ (4983/1024 : ℝ) ≤ (27321135690233/50000000000000000000 : ℝ) := by
    have hpowers : (1033/20000 : ℝ)^4983 ≤ (27321135690233/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1033 : ℕ)^4983*50000000000000000000^1024 ≤ 27321135690233^1024*20000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1033 20000 27321135690233 50000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1033/20000 : ℝ)) (X := (27321135690233/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23001/100000 : ℝ) ^ (4983/1024 : ℝ) ≤ (4897843628497581/6250000000000000000 : ℝ) := by
    have hpowers : (23001/100000 : ℝ)^4983 ≤ (4897843628497581/6250000000000000000 : ℝ)^1024 := by
      have hnat : (23001 : ℕ)^4983*6250000000000000000^1024 ≤ 4897843628497581^1024*100000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23001 100000 4897843628497581 6250000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23001/100000 : ℝ)) (X := (4897843628497581/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000027321135690233/25000000000000000000 : ℝ) ≤ (2500000561445531/2500000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (25000027321135690233/25000000000000000000 : ℝ)^1024 ≤ (2500000561445531/2500000000000000 : ℝ)^4983 := by
      have hnat : (25000027321135690233 : ℕ)^1024*2500000000000000^4983 ≤ 2500000561445531^4983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000027321135690233 25000000000000000000 2500000561445531 2500000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000561445531/2500000000000000 : ℝ)) (X := (25000027321135690233/25000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50039210070163670881/50000000000000000000 : ℝ) ≤ (10001611021860563/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (50039210070163670881/50000000000000000000 : ℝ)^1024 ≤ (10001611021860563/10000000000000000 : ℝ)^4983 := by
      have hnat : (50039210070163670881 : ℕ)^1024*10000000000000000^4983 ≤ 10001611021860563^4983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039210070163670881 50000000000000000000 10001611021860563 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001611021860563/10000000000000000 : ℝ)) (X := (50039210070163670881/50000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3129897843628497581/3125000000000000000 : ℝ) ≤ (5001609898969501/5000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (3129897843628497581/3125000000000000000 : ℝ)^1024 ≤ (5001609898969501/5000000000000000 : ℝ)^4983 := by
      have hnat : (3129897843628497581 : ℕ)^1024*5000000000000000^4983 ≤ 5001609898969501^4983*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3129897843628497581 3125000000000000000 5001609898969501 5000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001609898969501/5000000000000000 : ℝ)) (X := (3129897843628497581/3125000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27321135690233/50000000000000000000 : ℝ) ≤ ((89171710699439844397/89180000000000000000 : ℝ)+2*(1608776078439/1783600000000000 : ℝ)*(1033/20000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (89171710699439844397/89180000000000000000 : ℝ)+2*(1608776078439/1783600000000000 : ℝ)*(1033/20000 : ℝ)=(2500000561445531/2500000000000000 : ℝ) by norm_num, show 1+2*(27321135690233/50000000000000000000 : ℝ)=(25000027321135690233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4897843628497581/6250000000000000000 : ℝ)+(27321135690233/50000000000000000000 : ℝ) ≤ ((89171710699439844397/89180000000000000000 : ℝ)+(1608776078439/1783600000000000 : ℝ)*((23001/100000 : ℝ)+(1033/20000 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (89171710699439844397/89180000000000000000 : ℝ)+(1608776078439/1783600000000000 : ℝ)*((23001/100000 : ℝ)+(1033/20000 : ℝ))=(10001611021860563/10000000000000000 : ℝ) by norm_num, show 1+(4897843628497581/6250000000000000000 : ℝ)+(27321135690233/50000000000000000000 : ℝ)=(50039210070163670881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4897843628497581/6250000000000000000 : ℝ) ≤ ((89171710699439844397/89180000000000000000 : ℝ)+2*(1608776078439/1783600000000000 : ℝ)*(23001/100000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (89171710699439844397/89180000000000000000 : ℝ)+2*(1608776078439/1783600000000000 : ℝ)*(23001/100000 : ℝ)=(5001609898969501/5000000000000000 : ℝ) by norm_num, show 1+2*(4897843628497581/6250000000000000000 : ℝ)=(3129897843628497581/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89171710699439844397/89180000000000000000 : ℝ)*(X 1 0+X 2 0)+(1608776078439/1783600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (1033/20000 : ℝ)) (hi := (23001/100000 : ℝ)) (c := (89171710699439844397/89180000000000000000 : ℝ)) (alpha := (1608776078439/1783600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89171710699439844397/89180000000000000000 : ℝ)*(X 0 1+X 2 1)+(1608776078439/1783600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (1033/20000 : ℝ)) (hi := (23001/100000 : ℝ)) (c := (89171710699439844397/89180000000000000000 : ℝ)) (alpha := (1608776078439/1783600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89171710699439844397/89180000000000000000 : ℝ)*(X 0 2+X 1 2)+(1608776078439/1783600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (1033/20000 : ℝ)) (hi := (23001/100000 : ℝ)) (c := (89171710699439844397/89180000000000000000 : ℝ)) (alpha := (1608776078439/1783600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-312466383/2000000000 : ℝ)*X 0 0+(6855101/12500000 : ℝ)*X 0 1+(514889667/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356224701/10000000000 : ℝ)*X 1 0+(-868110801/5000000000 : ℝ)*X 1 1+(5148896397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678112069/5000000000 : ℝ)*X 2 0+(257444851/500000000 : ℝ)*X 2 1+(-1736221531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((416169317/1000000000 : ℝ)*X 0 0+(233464671/625000000 : ℝ)*X 0 1+(4621239911/10000000000 : ℝ)*X 0 2+(416169317/1000000000 : ℝ)*X 1 0+(233464671/625000000 : ℝ)*X 1 1+(4621239911/10000000000 : ℝ)*X 1 2+(416169317/1000000000 : ℝ)*X 2 0+(233464671/625000000 : ℝ)*X 2 1+(4621239911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-781233807/5000000000 : ℝ)*X 0 0+(257610591/500000000 : ℝ)*X 0 1+(5480720597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316615389/2500000000 : ℝ)*X 1 0+(-1404397979/10000000000 : ℝ)*X 1 1+(685090073/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316615387/2500000000 : ℝ)*X 2 0+(5480720593/10000000000 : ℝ)*X 2 1+(-702198989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4162052823/10000000000 : ℝ)*X 0 0+(4612479167/10000000000 : ℝ)*X 0 1+(748863169/2000000000 : ℝ)*X 0 2+(4162052823/10000000000 : ℝ)*X 1 0+(4612479167/10000000000 : ℝ)*X 1 1+(748863169/2000000000 : ℝ)*X 1 2+(4162052823/10000000000 : ℝ)*X 2 0+(4612479167/10000000000 : ℝ)*X 2 1+(748863169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (244803473920141626108777/44590000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118081483/6250000000000 : ℝ)*(base19) + (1410577757/100000000000000 : ℝ)*(base23) + (292400261/100000000000000 : ℝ)*(upper3) + (88447149/100000000000000 : ℝ)*(upper4) + (178170243/100000000000000 : ℝ)*(upper5) + (1028099917838463/50000000000000 : ℝ)*(major0) + (1028099917838463/50000000000000 : ℝ)*(major1) + (1028099917838463/50000000000000 : ℝ)*(major2) + (1491726429817983/50000000000000 : ℝ)*(sp0) + (2983467324542933/100000000000000 : ℝ)*(sp1) + (372933475408613/12500000000000 : ℝ)*(sp2) + (282230743860913/25000000000000 : ℝ)*(sp3) + (3270842139/20000000000000 : ℝ)*(sp4) + (3649530133/50000000000000 : ℝ)*(sp7) + (564465137251959/50000000000000 : ℝ)*(f.failure) + (2983469213846661/100000000000000 : ℝ)*(f.sum) + (138065579455837/44590000000000000000000000000 : ℝ)*base65 + (174570080530234861/91000000000000000000000000000000 : ℝ)*base68 + (310006204116765139/91000000000000000000000000000000 : ℝ)*base69 + (78142943942765139/91000000000000000000000000000000 : ℝ)*base71 + (45504119546737/44590000000000000000000000000 : ℝ)*base73 + (229772025910765139/91000000000000000000000000000000 : ℝ)*base75 + (617098577486234861/91000000000000000000000000000000 : ℝ)*base78 + (209586733110234861/91000000000000000000000000000000 : ℝ)*base80 + (108054878353637/44590000000000000000000000000 : ℝ)*base81 + (8349369/5000000000000000000000 : ℝ)*base90 + (8349369/5000000000000000000000 : ℝ)*base92 + (8349369/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29499807172546946989277934591/4459000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262621571/25000000000000 : ℝ)*(base19) + (561400123/50000000000000 : ℝ)*(base23) + (38150071/25000000000000 : ℝ)*(upper3) + (34309307/100000000000000 : ℝ)*(lower4) + (18781819/12500000000000 : ℝ)*(upper5) + (2097957675641533/100000000000000 : ℝ)*(major0) + (2097957675641533/100000000000000 : ℝ)*(major1) + (2097957675641533/100000000000000 : ℝ)*(major2) + (9589010007/100000000000000 : ℝ)*(sp1) + (2570218237/25000000000000 : ℝ)*(sp2) + (3044058247216083/100000000000000 : ℝ)*(sp4) + (190252975482487/6250000000000 : ℝ)*(sp5) + (304404684354289/10000000000000 : ℝ)*(sp6) + (575928441770319/50000000000000 : ℝ)*(sp7) + (575928441770319/50000000000000 : ℝ)*(f.failure) + (3044058247216083/100000000000000 : ℝ)*(f.sum) + (168592344081173/89180000000000000000000000000 : ℝ)*base66 + (2295441417198201849/182000000000000000000000000000000 : ℝ)*base67 + (1037515465188201849/182000000000000000000000000000000 : ℝ)*base69 + (1208932224884201849/182000000000000000000000000000000 : ℝ)*base71 + (538914345357467/89180000000000000000000000000 : ℝ)*base73 + (2284200585596201849/182000000000000000000000000000000 : ℝ)*base75 + (290794407014201849/182000000000000000000000000000000 : ℝ)*base77 + (1143227141258201849/182000000000000000000000000000000 : ℝ)*base79 + (328692798254627/89180000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (82364129/5000000000000000000000 : ℝ)*base90 + (82364129/5000000000000000000000 : ℝ)*base92 + (82364129/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1667_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3421/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1667_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1667_s2_0 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196268041/1250000000 : ℝ)*x 0 + (1361303757/2500000000 : ℝ)*x 1 + (5182592041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196268041/1250000000 : ℝ)^4987 ≤ (4865733498657/50000000000000 : ℝ)^3963 := by
    have hnat : (196268041 : ℕ)^4987*50000000000000^3963 ≤ 4865733498657^3963*1250000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196268041 1250000000 4865733498657 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361303757/2500000000 : ℝ)^4987 ≤ (5817199304853/12500000000000 : ℝ)^3963 := by
    have hnat : (1361303757 : ℕ)^4987*12500000000000^3963 ≤ 5817199304853^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361303757 2500000000 5817199304853 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182592041/10000000000 : ℝ)^4987 ≤ (43730938550567/100000000000000 : ℝ)^3963 := by
    have hnat : (5182592041 : ℕ)^4987*100000000000000^3963 ≤ 43730938550567^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182592041 10000000000 43730938550567 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196268041/1250000000 : ℝ), (1361303757/2500000000 : ℝ), (5182592041/10000000000 : ℝ)] ![(4865733498657/50000000000000 : ℝ), (5817199304853/12500000000000 : ℝ), (43730938550567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196268041/1250000000 : ℝ)|^4987 ≤ (4865733498657/50000000000000 : ℝ)^3963
        have hw : |(-196268041/1250000000 : ℝ)|=(196268041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361303757/2500000000 : ℝ)|^4987 ≤ (5817199304853/12500000000000 : ℝ)^3963
        have hw : |(1361303757/2500000000 : ℝ)|=(1361303757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182592041/10000000000 : ℝ)|^4987 ≤ (43730938550567/100000000000000 : ℝ)^3963
        have hw : |(5182592041/10000000000 : ℝ)|=(5182592041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_1 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345881427/10000000000 : ℝ)*x 0 + (-1705323627/10000000000 : ℝ)*x 1 + (1036518447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345881427/10000000000 : ℝ)^4987 ≤ (45471806148703/100000000000000 : ℝ)^3963 := by
    have hnat : (5345881427 : ℕ)^4987*100000000000000^3963 ≤ 45471806148703^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345881427 10000000000 45471806148703 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705323627/10000000000 : ℝ)^4987 ≤ (2159450646871/20000000000000 : ℝ)^3963 := by
    have hnat : (1705323627 : ℕ)^4987*20000000000000^3963 ≤ 2159450646871^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705323627 10000000000 2159450646871 20000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036518447/2000000000 : ℝ)^4987 ≤ (43730940610527/100000000000000 : ℝ)^3963 := by
    have hnat : (1036518447 : ℕ)^4987*100000000000000^3963 ≤ 43730940610527^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036518447 2000000000 43730940610527 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345881427/10000000000 : ℝ), (-1705323627/10000000000 : ℝ), (1036518447/2000000000 : ℝ)] ![(45471806148703/100000000000000 : ℝ), (2159450646871/20000000000000 : ℝ), (43730940610527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345881427/10000000000 : ℝ)|^4987 ≤ (45471806148703/100000000000000 : ℝ)^3963
        have hw : |(5345881427/10000000000 : ℝ)|=(5345881427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1705323627/10000000000 : ℝ)|^4987 ≤ (2159450646871/20000000000000 : ℝ)^3963
        have hw : |(-1705323627/10000000000 : ℝ)|=(1705323627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036518447/2000000000 : ℝ)|^4987 ≤ (43730940610527/100000000000000 : ℝ)^3963
        have hw : |(1036518447/2000000000 : ℝ)|=(1036518447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_2 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336470357/2500000000 : ℝ)*x 0 + (2591296051/5000000000 : ℝ)*x 1 + (-852661901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336470357/2500000000 : ℝ)^4987 ≤ (22735903079703/50000000000000 : ℝ)^3963 := by
    have hnat : (1336470357 : ℕ)^4987*50000000000000^3963 ≤ 22735903079703^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336470357 2500000000 22735903079703 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591296051/5000000000 : ℝ)^4987 ≤ (43730939198287/100000000000000 : ℝ)^3963 := by
    have hnat : (2591296051 : ℕ)^4987*100000000000000^3963 ≤ 43730939198287^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591296051 5000000000 43730939198287 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852661901/5000000000 : ℝ)^4987 ≤ (10797254628667/100000000000000 : ℝ)^3963 := by
    have hnat : (852661901 : ℕ)^4987*100000000000000^3963 ≤ 10797254628667^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852661901 5000000000 10797254628667 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336470357/2500000000 : ℝ), (2591296051/5000000000 : ℝ), (-852661901/5000000000 : ℝ)] ![(22735903079703/50000000000000 : ℝ), (43730939198287/100000000000000 : ℝ), (10797254628667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336470357/2500000000 : ℝ)|^4987 ≤ (22735903079703/50000000000000 : ℝ)^3963
        have hw : |(1336470357/2500000000 : ℝ)|=(1336470357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591296051/5000000000 : ℝ)|^4987 ≤ (43730939198287/100000000000000 : ℝ)^3963
        have hw : |(2591296051/5000000000 : ℝ)|=(2591296051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-852661901/5000000000 : ℝ)|^4987 ≤ (10797254628667/100000000000000 : ℝ)^3963
        have hw : |(-852661901/5000000000 : ℝ)|=(852661901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_3 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833508047/2000000000 : ℝ)*x 0 + (3830740343/10000000000 : ℝ)*x 1 + (4524784307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833508047/2000000000 : ℝ)^4987 ≤ (16619980363441/50000000000000 : ℝ)^3963 := by
    have hnat : (833508047 : ℕ)^4987*50000000000000^3963 ≤ 16619980363441^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833508047 2000000000 16619980363441 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3830740343/10000000000 : ℝ)^4987 ≤ (29895587402281/100000000000000 : ℝ)^3963 := by
    have hnat : (3830740343 : ℕ)^4987*100000000000000^3963 ≤ 29895587402281^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3830740343 10000000000 29895587402281 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524784307/10000000000 : ℝ)^4987 ≤ (18432225932581/50000000000000 : ℝ)^3963 := by
    have hnat : (4524784307 : ℕ)^4987*50000000000000^3963 ≤ 18432225932581^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524784307 10000000000 18432225932581 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833508047/2000000000 : ℝ), (3830740343/10000000000 : ℝ), (4524784307/10000000000 : ℝ)] ![(16619980363441/50000000000000 : ℝ), (29895587402281/100000000000000 : ℝ), (18432225932581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833508047/2000000000 : ℝ)|^4987 ≤ (16619980363441/50000000000000 : ℝ)^3963
        have hw : |(833508047/2000000000 : ℝ)|=(833508047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3830740343/10000000000 : ℝ)|^4987 ≤ (29895587402281/100000000000000 : ℝ)^3963
        have hw : |(3830740343/10000000000 : ℝ)|=(3830740343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524784307/10000000000 : ℝ)|^4987 ≤ (18432225932581/50000000000000 : ℝ)^3963
        have hw : |(4524784307/10000000000 : ℝ)|=(4524784307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_4 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-49069059/312500000 : ℝ)*x 0 + (5184632323/10000000000 : ℝ)*x 1 + (5443152893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49069059/312500000 : ℝ)^4987 ≤ (2432994580077/25000000000000 : ℝ)^3963 := by
    have hnat : (49069059 : ℕ)^4987*25000000000000^3963 ≤ 2432994580077^3963*312500000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49069059 312500000 2432994580077 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184632323/10000000000 : ℝ)^4987 ≤ (2734537755151/6250000000000 : ℝ)^3963 := by
    have hnat : (5184632323 : ℕ)^4987*6250000000000^3963 ≤ 2734537755151^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184632323 10000000000 2734537755151 6250000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443152893/10000000000 : ℝ)^4987 ≤ (11628854394969/25000000000000 : ℝ)^3963 := by
    have hnat : (5443152893 : ℕ)^4987*25000000000000^3963 ≤ 11628854394969^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443152893 10000000000 11628854394969 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49069059/312500000 : ℝ), (5184632323/10000000000 : ℝ), (5443152893/10000000000 : ℝ)] ![(2432994580077/25000000000000 : ℝ), (2734537755151/6250000000000 : ℝ), (11628854394969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49069059/312500000 : ℝ)|^4987 ≤ (2432994580077/25000000000000 : ℝ)^3963
        have hw : |(-49069059/312500000 : ℝ)|=(49069059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184632323/10000000000 : ℝ)|^4987 ≤ (2734537755151/6250000000000 : ℝ)^3963
        have hw : |(5184632323/10000000000 : ℝ)|=(5184632323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443152893/10000000000 : ℝ)|^4987 ≤ (11628854394969/25000000000000 : ℝ)^3963
        have hw : |(5443152893/10000000000 : ℝ)|=(5443152893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_5 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055118013/2000000000 : ℝ)*x 0 + (-361190713/2500000000 : ℝ)*x 1 + (5443153009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055118013/2000000000 : ℝ)^4987 ≤ (44720703423023/100000000000000 : ℝ)^3963 := by
    have hnat : (1055118013 : ℕ)^4987*100000000000000^3963 ≤ 44720703423023^3963*2000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055118013 2000000000 44720703423023 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361190713/2500000000 : ℝ)^4987 ≤ (2190969433829/25000000000000 : ℝ)^3963 := by
    have hnat : (361190713 : ℕ)^4987*25000000000000^3963 ≤ 2190969433829^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361190713 2500000000 2190969433829 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443153009/10000000000 : ℝ)^4987 ≤ (11628854706829/25000000000000 : ℝ)^3963 := by
    have hnat : (5443153009 : ℕ)^4987*25000000000000^3963 ≤ 11628854706829^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443153009 10000000000 11628854706829 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055118013/2000000000 : ℝ), (-361190713/2500000000 : ℝ), (5443153009/10000000000 : ℝ)] ![(44720703423023/100000000000000 : ℝ), (2190969433829/25000000000000 : ℝ), (11628854706829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055118013/2000000000 : ℝ)|^4987 ≤ (44720703423023/100000000000000 : ℝ)^3963
        have hw : |(1055118013/2000000000 : ℝ)|=(1055118013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361190713/2500000000 : ℝ)|^4987 ≤ (2190969433829/25000000000000 : ℝ)^3963
        have hw : |(-361190713/2500000000 : ℝ)|=(361190713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443153009/10000000000 : ℝ)|^4987 ≤ (11628854706829/25000000000000 : ℝ)^3963
        have hw : |(5443153009/10000000000 : ℝ)|=(5443153009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_6 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637795091/5000000000 : ℝ)*x 0 + (5443152831/10000000000 : ℝ)*x 1 + (-1444762939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637795091/5000000000 : ℝ)^4987 ≤ (11180176167773/25000000000000 : ℝ)^3963 := by
    have hnat : (2637795091 : ℕ)^4987*25000000000000^3963 ≤ 11180176167773^3963*5000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637795091 5000000000 11180176167773 25000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443152831/10000000000 : ℝ)^4987 ≤ (46515416913141/100000000000000 : ℝ)^3963 := by
    have hnat : (5443152831 : ℕ)^4987*100000000000000^3963 ≤ 46515416913141^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443152831 10000000000 46515416913141 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444762939/10000000000 : ℝ)^4987 ≤ (8763878399417/100000000000000 : ℝ)^3963 := by
    have hnat : (1444762939 : ℕ)^4987*100000000000000^3963 ≤ 8763878399417^3963*10000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444762939 10000000000 8763878399417 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637795091/5000000000 : ℝ), (5443152831/10000000000 : ℝ), (-1444762939/10000000000 : ℝ)] ![(11180176167773/25000000000000 : ℝ), (46515416913141/100000000000000 : ℝ), (8763878399417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637795091/5000000000 : ℝ)|^4987 ≤ (11180176167773/25000000000000 : ℝ)^3963
        have hw : |(2637795091/5000000000 : ℝ)|=(2637795091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443152831/10000000000 : ℝ)|^4987 ≤ (46515416913141/100000000000000 : ℝ)^3963
        have hw : |(5443152831/10000000000 : ℝ)|=(5443152831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1444762939/10000000000 : ℝ)|^4987 ≤ (8763878399417/100000000000000 : ℝ)^3963
        have hw : |(-1444762939/10000000000 : ℝ)|=(1444762939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1667_s2_7 (p : ℝ) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416771371/1000000000 : ℝ)*x 0 + (1129848191/2500000000 : ℝ)*x 1 + (959047439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416771371/1000000000 : ℝ)^4987 ≤ (33241701873037/100000000000000 : ℝ)^3963 := by
    have hnat : (416771371 : ℕ)^4987*100000000000000^3963 ≤ 33241701873037^3963*1000000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416771371 1000000000 33241701873037 100000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129848191/2500000000 : ℝ)^4987 ≤ (4601148020721/12500000000000 : ℝ)^3963 := by
    have hnat : (1129848191 : ℕ)^4987*12500000000000^3963 ≤ 4601148020721^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129848191 2500000000 4601148020721 12500000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959047439/2500000000 : ℝ)^4987 ≤ (14974556971497/50000000000000 : ℝ)^3963 := by
    have hnat : (959047439 : ℕ)^4987*50000000000000^3963 ≤ 14974556971497^3963*2500000000^4987 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959047439 2500000000 14974556971497 50000000000000 4987 3963 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4987/1024 : ℝ)) 4987 3963 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416771371/1000000000 : ℝ), (1129848191/2500000000 : ℝ), (959047439/2500000000 : ℝ)] ![(33241701873037/100000000000000 : ℝ), (4601148020721/12500000000000 : ℝ), (14974556971497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416771371/1000000000 : ℝ)|^4987 ≤ (33241701873037/100000000000000 : ℝ)^3963
        have hw : |(416771371/1000000000 : ℝ)|=(416771371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129848191/2500000000 : ℝ)|^4987 ≤ (4601148020721/12500000000000 : ℝ)^3963
        have hw : |(1129848191/2500000000 : ℝ)|=(1129848191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959047439/2500000000 : ℝ)|^4987 ≤ (14974556971497/50000000000000 : ℝ)^3963
        have hw : |(959047439/2500000000 : ℝ)|=(959047439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1667_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3421/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10703/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4073/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3421/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (399/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3421/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (399/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3421/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (399/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3421/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (399/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3421/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (399/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3421/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (399/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (399/4000 : ℝ) ^ (4983/1024 : ℝ) ≤ (672154375572739/50000000000000000000 : ℝ) := by
    have hpowers : (399/4000 : ℝ)^4983 ≤ (672154375572739/50000000000000000000 : ℝ)^1024 := by
      have hnat : (399 : ℕ)^4983*50000000000000000000^1024 ≤ 672154375572739^1024*4000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        399 4000 672154375572739 50000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (399/4000 : ℝ)) (X := (672154375572739/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3421/20000 : ℝ) ^ (4983/1024 : ℝ) ≤ (18544500370767703/100000000000000000000 : ℝ) := by
    have hpowers : (3421/20000 : ℝ)^4983 ≤ (18544500370767703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3421 : ℕ)^4983*100000000000000000000^1024 ≤ 18544500370767703^1024*20000^4983 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3421 20000 18544500370767703 100000000000000000000 4983 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3421/20000 : ℝ)) (X := (18544500370767703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000672154375572739/25000000000000000000 : ℝ) ≤ (10000055250148861/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (25000672154375572739/25000000000000000000 : ℝ)^1024 ≤ (10000055250148861/10000000000000000 : ℝ)^4983 := by
      have hnat : (25000672154375572739 : ℕ)^1024*10000000000000000^4983 ≤ 10000055250148861^4983*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000672154375572739 25000000000000000000 10000055250148861 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055250148861/10000000000000000 : ℝ)) (X := (25000672154375572739/25000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019888809121913181/100000000000000000000 : ℝ) ≤ (5000204340072603/5000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (100019888809121913181/100000000000000000000 : ℝ)^1024 ≤ (5000204340072603/5000000000000000 : ℝ)^4983 := by
      have hnat : (100019888809121913181 : ℕ)^1024*5000000000000000^4983 ≤ 5000204340072603^4983*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019888809121913181 100000000000000000000 5000204340072603 5000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000204340072603/5000000000000000 : ℝ)) (X := (100019888809121913181/100000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018544500370767703/50000000000000000000 : ℝ) ≤ (10000762110141551/10000000000000000 : ℝ) ^ (4983/1024 : ℝ) := by
    have hpowers : (50018544500370767703/50000000000000000000 : ℝ)^1024 ≤ (10000762110141551/10000000000000000 : ℝ)^4983 := by
      have hnat : (50018544500370767703 : ℕ)^1024*10000000000000000^4983 ≤ 10000762110141551^4983*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018544500370767703 50000000000000000000 10000762110141551 10000000000000000 1024 4983 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000762110141551/10000000000000000 : ℝ)) (X := (50018544500370767703/50000000000000000000 : ℝ)) (by norm_num) 4983 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(672154375572739/50000000000000000000 : ℝ) ≤ ((3564667150256714809/3565000000000000000 : ℝ)+2*(70685999269/142600000000000 : ℝ)*(399/4000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (3564667150256714809/3565000000000000000 : ℝ)+2*(70685999269/142600000000000 : ℝ)*(399/4000 : ℝ)=(10000055250148861/10000000000000000 : ℝ) by norm_num, show 1+2*(672154375572739/50000000000000000000 : ℝ)=(25000672154375572739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18544500370767703/100000000000000000000 : ℝ)+(672154375572739/50000000000000000000 : ℝ) ≤ ((3564667150256714809/3565000000000000000 : ℝ)+(70685999269/142600000000000 : ℝ)*((3421/20000 : ℝ)+(399/4000 : ℝ)))^(4983/1024 : ℝ) := by
    rw [show (3564667150256714809/3565000000000000000 : ℝ)+(70685999269/142600000000000 : ℝ)*((3421/20000 : ℝ)+(399/4000 : ℝ))=(5000204340072603/5000000000000000 : ℝ) by norm_num, show 1+(18544500370767703/100000000000000000000 : ℝ)+(672154375572739/50000000000000000000 : ℝ)=(100019888809121913181/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18544500370767703/100000000000000000000 : ℝ) ≤ ((3564667150256714809/3565000000000000000 : ℝ)+2*(70685999269/142600000000000 : ℝ)*(3421/20000 : ℝ))^(4983/1024 : ℝ) := by
    rw [show (3564667150256714809/3565000000000000000 : ℝ)+2*(70685999269/142600000000000 : ℝ)*(3421/20000 : ℝ)=(10000762110141551/10000000000000000 : ℝ) by norm_num, show 1+2*(18544500370767703/100000000000000000000 : ℝ)=(50018544500370767703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3564667150256714809/3565000000000000000 : ℝ)*(X 1 0+X 2 0)+(70685999269/142600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (3421/20000 : ℝ)) (c := (3564667150256714809/3565000000000000000 : ℝ)) (alpha := (70685999269/142600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3564667150256714809/3565000000000000000 : ℝ)*(X 0 1+X 2 1)+(70685999269/142600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (3421/20000 : ℝ)) (c := (3564667150256714809/3565000000000000000 : ℝ)) (alpha := (70685999269/142600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3564667150256714809/3565000000000000000 : ℝ)*(X 0 2+X 1 2)+(70685999269/142600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4983/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (3421/20000 : ℝ)) (c := (3564667150256714809/3565000000000000000 : ℝ)) (alpha := (70685999269/142600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196268041/1250000000 : ℝ)*X 0 0+(1361303757/2500000000 : ℝ)*X 0 1+(5182592041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345881427/10000000000 : ℝ)*X 1 0+(-1705323627/10000000000 : ℝ)*X 1 1+(1036518447/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336470357/2500000000 : ℝ)*X 2 0+(2591296051/5000000000 : ℝ)*X 2 1+(-852661901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((833508047/2000000000 : ℝ)*X 0 0+(3830740343/10000000000 : ℝ)*X 0 1+(4524784307/10000000000 : ℝ)*X 0 2+(833508047/2000000000 : ℝ)*X 1 0+(3830740343/10000000000 : ℝ)*X 1 1+(4524784307/10000000000 : ℝ)*X 1 2+(833508047/2000000000 : ℝ)*X 2 0+(3830740343/10000000000 : ℝ)*X 2 1+(4524784307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-49069059/312500000 : ℝ)*X 0 0+(5184632323/10000000000 : ℝ)*X 0 1+(5443152893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055118013/2000000000 : ℝ)*X 1 0+(-361190713/2500000000 : ℝ)*X 1 1+(5443153009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2637795091/5000000000 : ℝ)*X 2 0+(5443152831/10000000000 : ℝ)*X 2 1+(-1444762939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416771371/1000000000 : ℝ)*X 0 0+(1129848191/2500000000 : ℝ)*X 0 1+(959047439/2500000000 : ℝ)*X 0 2+(416771371/1000000000 : ℝ)*X 1 0+(1129848191/2500000000 : ℝ)*X 1 1+(959047439/2500000000 : ℝ)*X 1 2+(416771371/1000000000 : ℝ)*X 2 0+(1129848191/2500000000 : ℝ)*X 2 1+(959047439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1667_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (517323052507168445013448161/89125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223455441/25000000000000 : ℝ)*(base19) + (870668583/100000000000000 : ℝ)*(base23) + (12758193/100000000000000 : ℝ)*(lower2) + (215946349/100000000000000 : ℝ)*(upper3) + (28891977/50000000000000 : ℝ)*(upper5) + (1312151397021443/50000000000000 : ℝ)*(major0) + (1312151397021443/50000000000000 : ℝ)*(major1) + (1312151397021443/50000000000000 : ℝ)*(major2) + (951938592306233/25000000000000 : ℝ)*(sp0) + (1903882274118287/50000000000000 : ℝ)*(sp1) + (951941142847439/25000000000000 : ℝ)*(sp2) + (720417381263987/50000000000000 : ℝ)*(sp3) + (5536416703/50000000000000 : ℝ)*(sp4) + (162188039/3125000000000 : ℝ)*(sp7) + (720419976272611/50000000000000 : ℝ)*(f.failure) + (1903882721029169/50000000000000 : ℝ)*(f.sum) + (12144086769323/3565000000000000000000000000 : ℝ)*base66 + (693525684576824387/178250000000000000000000000000000 : ℝ)*base67 + (947029895590824387/178250000000000000000000000000000 : ℝ)*base69 + (355494509833175613/178250000000000000000000000000000 : ℝ)*base72 + (5979250576527/3565000000000000000000000000 : ℝ)*base73 + (97068253049175613/178250000000000000000000000000000 : ℝ)*base76 + (391347798610675613/178250000000000000000000000000000 : ℝ)*base78 + (1129766271426675613/178250000000000000000000000000000 : ℝ)*base80 + (5863999338557/3565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (36160499/5000000000000000000000 : ℝ)*base89 + (36160499/5000000000000000000000 : ℝ)*base91 + (36160499/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14866363660274394580589649/1437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (744828297/50000000000000 : ℝ)*(base19) + (1720335683/100000000000000 : ℝ)*(base23) + (240584107/100000000000000 : ℝ)*(upper3) + (67966289/100000000000000 : ℝ)*(lower4) + (99989183/50000000000000 : ℝ)*(upper5) + (666482081549601/25000000000000 : ℝ)*(major0) + (666482081549601/25000000000000 : ℝ)*(major1) + (666482081549601/25000000000000 : ℝ)*(major2) + (9270395669/50000000000000 : ℝ)*(sp1) + (19746244037/100000000000000 : ℝ)*(sp2) + (1934081194000697/50000000000000 : ℝ)*(sp4) + (1934071178776731/50000000000000 : ℝ)*(sp5) + (1934070460710837/50000000000000 : ℝ)*(sp6) + (292738783933627/20000000000000 : ℝ)*(sp7) + (292738783933627/20000000000000 : ℝ)*(f.failure) + (1934081194000697/50000000000000 : ℝ)*(f.sum) + (12616802433/7187500000000000000000000 : ℝ)*base65 + (26076917575265039/2875000000000000000000000000000 : ℝ)*base67 + (12846384637765039/2875000000000000000000000000000 : ℝ)*base69 + (8420013638765039/2875000000000000000000000000000 : ℝ)*base71 + (117817200887/28750000000000000000000000 : ℝ)*base73 + (31825424743015039/2875000000000000000000000000000 : ℝ)*base75 + (9971895088265039/2875000000000000000000000000000 : ℝ)*base77 + (28959977333015039/2875000000000000000000000000000 : ℝ)*base79 + (57788171949/57500000000000000000000000 : ℝ)*base81 + (3698357/2000000000000000000000 : ℝ)*base90 + (3698357/2000000000000000000000 : ℝ)*base92 + (3698357/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1667_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3421/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1667_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1667_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1667_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1667_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1667_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4983/1024 : ℝ) ≤ p) (hpb : p ≤ (4987/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (182137009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1667_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
