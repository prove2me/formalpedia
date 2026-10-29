-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:45:26.08337+00:00
-- url     : https://prove2.me/submissions/8ce77668-5a8e-4e96-aac0-754302f68619

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
theorem support_rectangle_w1325_s6_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-514685729/2500000000 : ℝ)*x 0 + (5413606689/10000000000 : ℝ)*x 1 + (1048810401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514685729/2500000000 : ℝ)^4285 ≤ (3133311041113/25000000000000 : ℝ)^3261 := by
    have hnat : (514685729 : ℕ)^4285*25000000000000^3261 ≤ 3133311041113^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514685729 2500000000 3133311041113 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413606689/10000000000 : ℝ)^4285 ≤ (22323781792643/50000000000000 : ℝ)^3261 := by
    have hnat : (5413606689 : ℕ)^4285*50000000000000^3261 ≤ 22323781792643^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413606689 10000000000 22323781792643 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048810401/2000000000 : ℝ)^4285 ≤ (8563838448573/20000000000000 : ℝ)^3261 := by
    have hnat : (1048810401 : ℕ)^4285*20000000000000^3261 ≤ 8563838448573^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048810401 2000000000 8563838448573 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514685729/2500000000 : ℝ), (5413606689/10000000000 : ℝ), (1048810401/2000000000 : ℝ)] ![(3133311041113/25000000000000 : ℝ), (22323781792643/50000000000000 : ℝ), (8563838448573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514685729/2500000000 : ℝ)|^4285 ≤ (3133311041113/25000000000000 : ℝ)^3261
        have hw : |(-514685729/2500000000 : ℝ)|=(514685729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413606689/10000000000 : ℝ)|^4285 ≤ (22323781792643/50000000000000 : ℝ)^3261
        have hw : |(5413606689/10000000000 : ℝ)|=(5413606689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048810401/2000000000 : ℝ)|^4285 ≤ (8563838448573/20000000000000 : ℝ)^3261
        have hw : |(1048810401/2000000000 : ℝ)|=(1048810401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674645269/5000000000 : ℝ)*x 0 + (-2145146497/10000000000 : ℝ)*x 1 + (1311012977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674645269/5000000000 : ℝ)^4285 ≤ (5493983735981/12500000000000 : ℝ)^3261 := by
    have hnat : (2674645269 : ℕ)^4285*12500000000000^3261 ≤ 5493983735981^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674645269 5000000000 5493983735981 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145146497/10000000000 : ℝ)^4285 ≤ (13228938891179/100000000000000 : ℝ)^3261 := by
    have hnat : (2145146497 : ℕ)^4285*100000000000000^3261 ≤ 13228938891179^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145146497 10000000000 13228938891179 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311012977/2500000000 : ℝ)^4285 ≤ (21409595601061/50000000000000 : ℝ)^3261 := by
    have hnat : (1311012977 : ℕ)^4285*50000000000000^3261 ≤ 21409595601061^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311012977 2500000000 21409595601061 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674645269/5000000000 : ℝ), (-2145146497/10000000000 : ℝ), (1311012977/2500000000 : ℝ)] ![(5493983735981/12500000000000 : ℝ), (13228938891179/100000000000000 : ℝ), (21409595601061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674645269/5000000000 : ℝ)|^4285 ≤ (5493983735981/12500000000000 : ℝ)^3261
        have hw : |(2674645269/5000000000 : ℝ)|=(2674645269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145146497/10000000000 : ℝ)|^4285 ≤ (13228938891179/100000000000000 : ℝ)^3261
        have hw : |(-2145146497/10000000000 : ℝ)|=(2145146497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311012977/2500000000 : ℝ)|^4285 ≤ (21409595601061/50000000000000 : ℝ)^3261
        have hw : |(1311012977/2500000000 : ℝ)|=(1311012977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069858077/2000000000 : ℝ)*x 0 + (5244051887/10000000000 : ℝ)*x 1 + (-2145146729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069858077/2000000000 : ℝ)^4285 ≤ (4395186823599/10000000000000 : ℝ)^3261 := by
    have hnat : (1069858077 : ℕ)^4285*10000000000000^3261 ≤ 4395186823599^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069858077 2000000000 4395186823599 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244051887/10000000000 : ℝ)^4285 ≤ (42819190976807/100000000000000 : ℝ)^3261 := by
    have hnat : (5244051887 : ℕ)^4285*100000000000000^3261 ≤ 42819190976807^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244051887 10000000000 42819190976807 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145146729/10000000000 : ℝ)^4285 ≤ (13228940771171/100000000000000 : ℝ)^3261 := by
    have hnat : (2145146729 : ℕ)^4285*100000000000000^3261 ≤ 13228940771171^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145146729 10000000000 13228940771171 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069858077/2000000000 : ℝ), (5244051887/10000000000 : ℝ), (-2145146729/10000000000 : ℝ)] ![(4395186823599/10000000000000 : ℝ), (42819190976807/100000000000000 : ℝ), (13228940771171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069858077/2000000000 : ℝ)|^4285 ≤ (4395186823599/10000000000000 : ℝ)^3261
        have hw : |(1069858077/2000000000 : ℝ)|=(1069858077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244051887/10000000000 : ℝ)|^4285 ≤ (42819190976807/100000000000000 : ℝ)^3261
        have hw : |(5244051887/10000000000 : ℝ)|=(5244051887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145146729/10000000000 : ℝ)|^4285 ≤ (13228940771171/100000000000000 : ℝ)^3261
        have hw : |(-2145146729/10000000000 : ℝ)|=(2145146729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331081583/10000000000 : ℝ)*x 0 + (207901443/500000000 : ℝ)*x 1 + (4510903393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331081583/10000000000 : ℝ)^4285 ≤ (16651466999877/50000000000000 : ℝ)^3261 := by
    have hnat : (4331081583 : ℕ)^4285*50000000000000^3261 ≤ 16651466999877^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331081583 10000000000 16651466999877 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207901443/500000000 : ℝ)^4285 ≤ (986422159279/3125000000000 : ℝ)^3261 := by
    have hnat : (207901443 : ℕ)^4285*3125000000000^3261 ≤ 986422159279^3261*500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207901443 500000000 986422159279 3125000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510903393/10000000000 : ℝ)^4285 ≤ (35131556892001/100000000000000 : ℝ)^3261 := by
    have hnat : (4510903393 : ℕ)^4285*100000000000000^3261 ≤ 35131556892001^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510903393 10000000000 35131556892001 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331081583/10000000000 : ℝ), (207901443/500000000 : ℝ), (4510903393/10000000000 : ℝ)] ![(16651466999877/50000000000000 : ℝ), (986422159279/3125000000000 : ℝ), (35131556892001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331081583/10000000000 : ℝ)|^4285 ≤ (16651466999877/50000000000000 : ℝ)^3261
        have hw : |(4331081583/10000000000 : ℝ)|=(4331081583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207901443/500000000 : ℝ)|^4285 ≤ (986422159279/3125000000000 : ℝ)^3261
        have hw : |(207901443/500000000 : ℝ)|=(207901443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510903393/10000000000 : ℝ)|^4285 ≤ (35131556892001/100000000000000 : ℝ)^3261
        have hw : |(4510903393/10000000000 : ℝ)|=(4510903393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2058755459/10000000000 : ℝ)*x 0 + (1311164569/2500000000 : ℝ)*x 1 + (1082599433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058755459/10000000000 : ℝ)^4285 ≤ (6266672250973/50000000000000 : ℝ)^3261 := by
    have hnat : (2058755459 : ℕ)^4285*50000000000000^3261 ≤ 6266672250973^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058755459 10000000000 6266672250973 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311164569/2500000000 : ℝ)^4285 ≤ (21412848613081/50000000000000 : ℝ)^3261 := by
    have hnat : (1311164569 : ℕ)^4285*50000000000000^3261 ≤ 21412848613081^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311164569 2500000000 21412848613081 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082599433/2000000000 : ℝ)^4285 ≤ (4464095825977/10000000000000 : ℝ)^3261 := by
    have hnat : (1082599433 : ℕ)^4285*10000000000000^3261 ≤ 4464095825977^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082599433 2000000000 4464095825977 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2058755459/10000000000 : ℝ), (1311164569/2500000000 : ℝ), (1082599433/2000000000 : ℝ)] ![(6266672250973/50000000000000 : ℝ), (21412848613081/50000000000000 : ℝ), (4464095825977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2058755459/10000000000 : ℝ)|^4285 ≤ (6266672250973/50000000000000 : ℝ)^3261
        have hw : |(-2058755459/10000000000 : ℝ)|=(2058755459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311164569/2500000000 : ℝ)|^4285 ≤ (21412848613081/50000000000000 : ℝ)^3261
        have hw : |(1311164569/2500000000 : ℝ)|=(1311164569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082599433/2000000000 : ℝ)|^4285 ≤ (4464095825977/10000000000000 : ℝ)^3261
        have hw : |(1082599433/2000000000 : ℝ)|=(1082599433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530570383/1000000000 : ℝ)*x 0 + (-1976201443/10000000000 : ℝ)*x 1 + (676624641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530570383/1000000000 : ℝ)^4285 ≤ (43481891083857/100000000000000 : ℝ)^3261 := by
    have hnat : (530570383 : ℕ)^4285*100000000000000^3261 ≤ 43481891083857^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530570383 1000000000 43481891083857 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976201443/10000000000 : ℝ)^4285 ≤ (5938575523059/50000000000000 : ℝ)^3261 := by
    have hnat : (1976201443 : ℕ)^4285*50000000000000^3261 ≤ 5938575523059^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976201443 10000000000 5938575523059 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676624641/1250000000 : ℝ)^4285 ≤ (44640957858813/100000000000000 : ℝ)^3261 := by
    have hnat : (676624641 : ℕ)^4285*100000000000000^3261 ≤ 44640957858813^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676624641 1250000000 44640957858813 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530570383/1000000000 : ℝ), (-1976201443/10000000000 : ℝ), (676624641/1250000000 : ℝ)] ![(43481891083857/100000000000000 : ℝ), (5938575523059/50000000000000 : ℝ), (44640957858813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530570383/1000000000 : ℝ)|^4285 ≤ (43481891083857/100000000000000 : ℝ)^3261
        have hw : |(530570383/1000000000 : ℝ)|=(530570383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976201443/10000000000 : ℝ)|^4285 ≤ (5938575523059/50000000000000 : ℝ)^3261
        have hw : |(-1976201443/10000000000 : ℝ)|=(1976201443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676624641/1250000000 : ℝ)|^4285 ≤ (44640957858813/100000000000000 : ℝ)^3261
        have hw : |(676624641/1250000000 : ℝ)|=(676624641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305703821/10000000000 : ℝ)*x 0 + (1353249289/2500000000 : ℝ)*x 1 + (-247025177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305703821/10000000000 : ℝ)^4285 ≤ (21740945493469/50000000000000 : ℝ)^3261 := by
    have hnat : (5305703821 : ℕ)^4285*50000000000000^3261 ≤ 21740945493469^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305703821 10000000000 21740945493469 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353249289/2500000000 : ℝ)^4285 ≤ (139502994257/312500000000 : ℝ)^3261 := by
    have hnat : (1353249289 : ℕ)^4285*312500000000^3261 ≤ 139502994257^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353249289 2500000000 139502994257 312500000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247025177/1250000000 : ℝ)^4285 ≤ (11877150832889/100000000000000 : ℝ)^3261 := by
    have hnat : (247025177 : ℕ)^4285*100000000000000^3261 ≤ 11877150832889^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247025177 1250000000 11877150832889 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305703821/10000000000 : ℝ), (1353249289/2500000000 : ℝ), (-247025177/1250000000 : ℝ)] ![(21740945493469/50000000000000 : ℝ), (139502994257/312500000000 : ℝ), (11877150832889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305703821/10000000000 : ℝ)|^4285 ≤ (21740945493469/50000000000000 : ℝ)^3261
        have hw : |(5305703821/10000000000 : ℝ)|=(5305703821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353249289/2500000000 : ℝ)|^4285 ≤ (139502994257/312500000000 : ℝ)^3261
        have hw : |(1353249289/2500000000 : ℝ)|=(1353249289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247025177/1250000000 : ℝ)|^4285 ≤ (11877150832889/100000000000000 : ℝ)^3261
        have hw : |(-247025177/1250000000 : ℝ)|=(247025177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s6_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433110737/1000000000 : ℝ)*x 0 + (4509641383/10000000000 : ℝ)*x 1 + (415929733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433110737/1000000000 : ℝ)^4285 ≤ (1665159727377/5000000000000 : ℝ)^3261 := by
    have hnat : (433110737 : ℕ)^4285*5000000000000^3261 ≤ 1665159727377^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433110737 1000000000 1665159727377 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509641383/10000000000 : ℝ)^4285 ≤ (35118642391437/100000000000000 : ℝ)^3261 := by
    have hnat : (4509641383 : ℕ)^4285*100000000000000^3261 ≤ 35118642391437^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509641383 10000000000 35118642391437 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415929733/1000000000 : ℝ)^4285 ≤ (31578163053109/100000000000000 : ℝ)^3261 := by
    have hnat : (415929733 : ℕ)^4285*100000000000000^3261 ≤ 31578163053109^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415929733 1000000000 31578163053109 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433110737/1000000000 : ℝ), (4509641383/10000000000 : ℝ), (415929733/1000000000 : ℝ)] ![(1665159727377/5000000000000 : ℝ), (35118642391437/100000000000000 : ℝ), (31578163053109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433110737/1000000000 : ℝ)|^4285 ≤ (1665159727377/5000000000000 : ℝ)^3261
        have hw : |(433110737/1000000000 : ℝ)|=(433110737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509641383/10000000000 : ℝ)|^4285 ≤ (35118642391437/100000000000000 : ℝ)^3261
        have hw : |(4509641383/10000000000 : ℝ)|=(4509641383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415929733/1000000000 : ℝ)|^4285 ≤ (31578163053109/100000000000000 : ℝ)^3261
        have hw : |(415929733/1000000000 : ℝ)|=(415929733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2777/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14697/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11099/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (10135740608912911/100000000000000000000 : ℝ) := by
    have hpowers : (11099/100000 : ℝ)^1071 ≤ (10135740608912911/100000000000000000000 : ℝ)^256 := by
      have hnat : (11099 : ℕ)^1071*100000000000000000000^256 ≤ 10135740608912911^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11099 100000 10135740608912911 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11099/100000 : ℝ)) (X := (10135740608912911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (1071/256 : ℝ) ≤ (3289542117349481/10000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^1071 ≤ (3289542117349481/10000000000000000000 : ℝ)^256 := by
      have hnat : (7353 : ℕ)^1071*10000000000000000000^256 ≤ 3289542117349481^256*50000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 3289542117349481 10000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (3289542117349481/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010135740608912911/50000000000000000000 : ℝ) ≤ (5000242254854017/5000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50010135740608912911/50000000000000000000 : ℝ)^256 ≤ (5000242254854017/5000000000000000 : ℝ)^1071 := by
      have hnat : (50010135740608912911 : ℕ)^256*5000000000000000^1071 ≤ 5000242254854017^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010135740608912911 50000000000000000000 5000242254854017 5000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000242254854017/5000000000000000 : ℝ)) (X := (50010135740608912911/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043031161782407721/100000000000000000000 : ℝ) ≤ (10001028400957519/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (100043031161782407721/100000000000000000000 : ℝ)^256 ≤ (10001028400957519/10000000000000000 : ℝ)^1071 := by
      have hnat : (100043031161782407721 : ℕ)^256*10000000000000000^1071 ≤ 10001028400957519^1071*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043031161782407721 100000000000000000000 10001028400957519 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001028400957519/10000000000000000 : ℝ)) (X := (100043031161782407721/100000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003289542117349481/5000000000000000000 : ℝ) ≤ (2500393073051751/2500000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (5003289542117349481/5000000000000000000 : ℝ)^256 ≤ (2500393073051751/2500000000000000 : ℝ)^1071 := by
      have hnat : (5003289542117349481 : ℕ)^256*2500000000000000^1071 ≤ 2500393073051751^1071*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003289542117349481 5000000000000000000 2500393073051751 2500000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500393073051751/2500000000000000 : ℝ)) (X := (5003289542117349481/5000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10135740608912911/100000000000000000000 : ℝ) ≤ ((2253729645535050663/2254375000000000000 : ℝ)+2*(108778249897/72140000000000 : ℝ)*(11099/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (2253729645535050663/2254375000000000000 : ℝ)+2*(108778249897/72140000000000 : ℝ)*(11099/100000 : ℝ)=(5000242254854017/5000000000000000 : ℝ) by norm_num, show 1+2*(10135740608912911/100000000000000000000 : ℝ)=(50010135740608912911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3289542117349481/10000000000000000000 : ℝ)+(10135740608912911/100000000000000000000 : ℝ) ≤ ((2253729645535050663/2254375000000000000 : ℝ)+(108778249897/72140000000000 : ℝ)*((7353/50000 : ℝ)+(11099/100000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (2253729645535050663/2254375000000000000 : ℝ)+(108778249897/72140000000000 : ℝ)*((7353/50000 : ℝ)+(11099/100000 : ℝ))=(10001028400957519/10000000000000000 : ℝ) by norm_num, show 1+(3289542117349481/10000000000000000000 : ℝ)+(10135740608912911/100000000000000000000 : ℝ)=(100043031161782407721/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3289542117349481/10000000000000000000 : ℝ) ≤ ((2253729645535050663/2254375000000000000 : ℝ)+2*(108778249897/72140000000000 : ℝ)*(7353/50000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (2253729645535050663/2254375000000000000 : ℝ)+2*(108778249897/72140000000000 : ℝ)*(7353/50000 : ℝ)=(2500393073051751/2500000000000000 : ℝ) by norm_num, show 1+2*(3289542117349481/10000000000000000000 : ℝ)=(5003289542117349481/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2253729645535050663/2254375000000000000 : ℝ)*(X 1 0+X 2 0)+(108778249897/72140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (2253729645535050663/2254375000000000000 : ℝ)) (alpha := (108778249897/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2253729645535050663/2254375000000000000 : ℝ)*(X 0 1+X 2 1)+(108778249897/72140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (2253729645535050663/2254375000000000000 : ℝ)) (alpha := (108778249897/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2253729645535050663/2254375000000000000 : ℝ)*(X 0 2+X 1 2)+(108778249897/72140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (2253729645535050663/2254375000000000000 : ℝ)) (alpha := (108778249897/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-514685729/2500000000 : ℝ)*X 0 0+(5413606689/10000000000 : ℝ)*X 0 1+(1048810401/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674645269/5000000000 : ℝ)*X 1 0+(-2145146497/10000000000 : ℝ)*X 1 1+(1311012977/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069858077/2000000000 : ℝ)*X 2 0+(5244051887/10000000000 : ℝ)*X 2 1+(-2145146729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331081583/10000000000 : ℝ)*X 0 0+(207901443/500000000 : ℝ)*X 0 1+(4510903393/10000000000 : ℝ)*X 0 2+(4331081583/10000000000 : ℝ)*X 1 0+(207901443/500000000 : ℝ)*X 1 1+(4510903393/10000000000 : ℝ)*X 1 2+(4331081583/10000000000 : ℝ)*X 2 0+(207901443/500000000 : ℝ)*X 2 1+(4510903393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2058755459/10000000000 : ℝ)*X 0 0+(1311164569/2500000000 : ℝ)*X 0 1+(1082599433/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530570383/1000000000 : ℝ)*X 1 0+(-1976201443/10000000000 : ℝ)*X 1 1+(676624641/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305703821/10000000000 : ℝ)*X 2 0+(1353249289/2500000000 : ℝ)*X 2 1+(-247025177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433110737/1000000000 : ℝ)*X 0 0+(4509641383/10000000000 : ℝ)*X 0 1+(415929733/1000000000 : ℝ)*X 0 2+(433110737/1000000000 : ℝ)*X 1 0+(4509641383/10000000000 : ℝ)*X 1 1+(415929733/1000000000 : ℝ)*X 1 2+(433110737/1000000000 : ℝ)*X 2 0+(4509641383/10000000000 : ℝ)*X 2 1+(415929733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133827453824608828799665101/28179687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (710648929/100000000000000 : ℝ)*(base19) + (735800471/100000000000000 : ℝ)*(base23) + (33387613/50000000000000 : ℝ)*(upper3) + (22999953/20000000000000 : ℝ)*(lower4) + (1091464942197717/25000000000000 : ℝ)*(major0) + (1091464942197717/25000000000000 : ℝ)*(major1) + (1091464942197717/25000000000000 : ℝ)*(major2) + (589782134321403/10000000000000 : ℝ)*(sp0) + (5897833299203577/100000000000000 : ℝ)*(sp1) + (1474457669882709/25000000000000 : ℝ)*(sp2) + (1416938583532747/50000000000000 : ℝ)*(sp3) + (3166659619/25000000000000 : ℝ)*(sp4) + (6486303/250000000000 : ℝ)*(sp6) + (8202361223/100000000000000 : ℝ)*(sp7) + (2833885369426717/100000000000000 : ℝ)*(f.failure) + (2948917004926253/50000000000000 : ℝ)*(f.sum) + (121673651449/90175000000000000000000000 : ℝ)*base65 + (3493121493519249/14089843750000000000000000000000 : ℝ)*base67 + (475361256933563629/56359375000000000000000000000000 : ℝ)*base70 + (513305686108751129/56359375000000000000000000000000 : ℝ)*base72 + (2975987703309/901750000000000000000000000 : ℝ)*base73 + (194337870733282379/56359375000000000000000000000000 : ℝ)*base76 + (200480869246844879/56359375000000000000000000000000 : ℝ)*base78 + (268107267281727127/28179687500000000000000000000000 : ℝ)*base80 + (442049260809/180350000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3302251/625000000000000000000 : ℝ)*base90 + (3302251/625000000000000000000 : ℝ)*base92 + (3302251/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (484316740147686941976308661/56359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375483543/25000000000000 : ℝ)*(base19) + (100849747/6250000000000 : ℝ)*(base23) + (42547079/25000000000000 : ℝ)*(upper3) + (5140883/10000000000000 : ℝ)*(lower4) + (16791289/10000000000000 : ℝ)*(upper5) + (68708858376257/1562500000000 : ℝ)*(major0) + (68708858376257/1562500000000 : ℝ)*(major1) + (68708858376257/1562500000000 : ℝ)*(major2) + (7351049217/25000000000000 : ℝ)*(sp1) + (32428611247/100000000000000 : ℝ)*(sp2) + (5940396872190897/100000000000000 : ℝ)*(sp4) + (5940365966059857/100000000000000 : ℝ)*(sp5) + (5940362829983697/100000000000000 : ℝ)*(sp6) + (1427168356762229/50000000000000 : ℝ)*(sp7) + (1427168356762229/50000000000000 : ℝ)*(f.failure) + (5940396872190897/100000000000000 : ℝ)*(f.sum) + (9700087130503/3607000000000000000000000000 : ℝ)*base66 + (84401253815579747/28179687500000000000000000000000 : ℝ)*base68 + (171656295673324881/56359375000000000000000000000000 : ℝ)*base69 + (62479817496642247/28179687500000000000000000000000 : ℝ)*base72 + (11261563309913/3607000000000000000000000000 : ℝ)*base74 + (62200497803719561/14089843750000000000000000000000 : ℝ)*base76 + (8672201786754109/3522460937500000000000000000000 : ℝ)*base78 + (743981234975981131/56359375000000000000000000000000 : ℝ)*base79 + (991340815981/3607000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4085613/312500000000000000000 : ℝ)*base89 + (4085613/312500000000000000000 : ℝ)*base91 + (4085613/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s7_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-514687929/2500000000 : ℝ)*x 0 + (10573303/19531250 : ℝ)*x 1 + (1048824351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514687929/2500000000 : ℝ)^4285 ≤ (12533314559867/100000000000000 : ℝ)^3261 := by
    have hnat : (514687929 : ℕ)^4285*100000000000000^3261 ≤ 12533314559867^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514687929 2500000000 12533314559867 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10573303/19531250 : ℝ)^4285 ≤ (22323372407707/50000000000000 : ℝ)^3261 := by
    have hnat : (10573303 : ℕ)^4285*50000000000000^3261 ≤ 22323372407707^3261*19531250^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10573303 19531250 22323372407707 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048824351/2000000000 : ℝ)^4285 ≤ (10704985153327/25000000000000 : ℝ)^3261 := by
    have hnat : (1048824351 : ℕ)^4285*25000000000000^3261 ≤ 10704985153327^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048824351 2000000000 10704985153327 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514687929/2500000000 : ℝ), (10573303/19531250 : ℝ), (1048824351/2000000000 : ℝ)] ![(12533314559867/100000000000000 : ℝ), (22323372407707/50000000000000 : ℝ), (10704985153327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514687929/2500000000 : ℝ)|^4285 ≤ (12533314559867/100000000000000 : ℝ)^3261
        have hw : |(-514687929/2500000000 : ℝ)|=(514687929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10573303/19531250 : ℝ)|^4285 ≤ (22323372407707/50000000000000 : ℝ)^3261
        have hw : |(10573303/19531250 : ℝ)|=(10573303/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048824351/2000000000 : ℝ)|^4285 ≤ (10704985153327/25000000000000 : ℝ)^3261
        have hw : |(1048824351/2000000000 : ℝ)|=(1048824351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674635123/5000000000 : ℝ)*x 0 + (-429015529/2000000000 : ℝ)*x 1 + (655515541/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674635123/5000000000 : ℝ)^4285 ≤ (1373489087697/3125000000000 : ℝ)^3261 := by
    have hnat : (2674635123 : ℕ)^4285*3125000000000^3261 ≤ 1373489087697^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674635123 5000000000 1373489087697 3125000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429015529/2000000000 : ℝ)^4285 ≤ (13228380957661/100000000000000 : ℝ)^3261 := by
    have hnat : (429015529 : ℕ)^4285*100000000000000^3261 ≤ 13228380957661^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429015529 2000000000 13228380957661 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655515541/1250000000 : ℝ)^4285 ≤ (21409984109961/50000000000000 : ℝ)^3261 := by
    have hnat : (655515541 : ℕ)^4285*50000000000000^3261 ≤ 21409984109961^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655515541 1250000000 21409984109961 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674635123/5000000000 : ℝ), (-429015529/2000000000 : ℝ), (655515541/1250000000 : ℝ)] ![(1373489087697/3125000000000 : ℝ), (13228380957661/100000000000000 : ℝ), (21409984109961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674635123/5000000000 : ℝ)|^4285 ≤ (1373489087697/3125000000000 : ℝ)^3261
        have hw : |(2674635123/5000000000 : ℝ)|=(2674635123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429015529/2000000000 : ℝ)|^4285 ≤ (13228380957661/100000000000000 : ℝ)^3261
        have hw : |(-429015529/2000000000 : ℝ)|=(429015529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655515541/1250000000 : ℝ)|^4285 ≤ (21409984109961/50000000000000 : ℝ)^3261
        have hw : |(655515541/1250000000 : ℝ)|=(655515541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337317957/2500000000 : ℝ)*x 0 + (5244122657/10000000000 : ℝ)*x 1 + (-2145077751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337317957/2500000000 : ℝ)^4285 ≤ (43951667886277/100000000000000 : ℝ)^3261 := by
    have hnat : (1337317957 : ℕ)^4285*100000000000000^3261 ≤ 43951667886277^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337317957 2500000000 43951667886277 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244122657/10000000000 : ℝ)^4285 ≤ (2140997514559/5000000000000 : ℝ)^3261 := by
    have hnat : (5244122657 : ℕ)^4285*5000000000000^3261 ≤ 2140997514559^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244122657 10000000000 2140997514559 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145077751/10000000000 : ℝ)^4285 ≤ (6614190908307/50000000000000 : ℝ)^3261 := by
    have hnat : (2145077751 : ℕ)^4285*50000000000000^3261 ≤ 6614190908307^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145077751 10000000000 6614190908307 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337317957/2500000000 : ℝ), (5244122657/10000000000 : ℝ), (-2145077751/10000000000 : ℝ)] ![(43951667886277/100000000000000 : ℝ), (2140997514559/5000000000000 : ℝ), (6614190908307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337317957/2500000000 : ℝ)|^4285 ≤ (43951667886277/100000000000000 : ℝ)^3261
        have hw : |(1337317957/2500000000 : ℝ)|=(1337317957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244122657/10000000000 : ℝ)|^4285 ≤ (2140997514559/5000000000000 : ℝ)^3261
        have hw : |(5244122657/10000000000 : ℝ)|=(5244122657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145077751/10000000000 : ℝ)|^4285 ≤ (6614190908307/50000000000000 : ℝ)^3261
        have hw : |(-2145077751/10000000000 : ℝ)|=(2145077751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33836607/78125000 : ℝ)*x 0 + (2079092127/5000000000 : ℝ)*x 1 + (225537393/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33836607/78125000 : ℝ)^4285 ≤ (16651487778413/50000000000000 : ℝ)^3261 := by
    have hnat : (33836607 : ℕ)^4285*50000000000000^3261 ≤ 16651487778413^3261*78125000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33836607 78125000 16651487778413 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079092127/5000000000 : ℝ)^4285 ≤ (31567059205509/100000000000000 : ℝ)^3261 := by
    have hnat : (2079092127 : ℕ)^4285*100000000000000^3261 ≤ 31567059205509^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079092127 5000000000 31567059205509 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225537393/500000000 : ℝ)^4285 ≤ (35129965218099/100000000000000 : ℝ)^3261 := by
    have hnat : (225537393 : ℕ)^4285*100000000000000^3261 ≤ 35129965218099^3261*500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225537393 500000000 35129965218099 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33836607/78125000 : ℝ), (2079092127/5000000000 : ℝ), (225537393/500000000 : ℝ)] ![(16651487778413/50000000000000 : ℝ), (31567059205509/100000000000000 : ℝ), (35129965218099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33836607/78125000 : ℝ)|^4285 ≤ (16651487778413/50000000000000 : ℝ)^3261
        have hw : |(33836607/78125000 : ℝ)|=(33836607/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079092127/5000000000 : ℝ)|^4285 ≤ (31567059205509/100000000000000 : ℝ)^3261
        have hw : |(2079092127/5000000000 : ℝ)|=(2079092127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225537393/500000000 : ℝ)|^4285 ≤ (35129965218099/100000000000000 : ℝ)^3261
        have hw : |(225537393/500000000 : ℝ)|=(225537393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411752609/2000000000 : ℝ)*x 0 + (209789149/400000000 : ℝ)*x 1 + (5412921811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411752609/2000000000 : ℝ)^4285 ≤ (1566675648263/12500000000000 : ℝ)^3261 := by
    have hnat : (411752609 : ℕ)^4285*12500000000000^3261 ≤ 1566675648263^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411752609 2000000000 1566675648263 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209789149/400000000 : ℝ)^4285 ≤ (42826453123859/100000000000000 : ℝ)^3261 := by
    have hnat : (209789149 : ℕ)^4285*100000000000000^3261 ≤ 42826453123859^3261*400000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209789149 400000000 42826453123859 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412921811/10000000000 : ℝ)^4285 ≤ (22320070837667/50000000000000 : ℝ)^3261 := by
    have hnat : (5412921811 : ℕ)^4285*50000000000000^3261 ≤ 22320070837667^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412921811 10000000000 22320070837667 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411752609/2000000000 : ℝ), (209789149/400000000 : ℝ), (5412921811/10000000000 : ℝ)] ![(1566675648263/12500000000000 : ℝ), (42826453123859/100000000000000 : ℝ), (22320070837667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411752609/2000000000 : ℝ)|^4285 ≤ (1566675648263/12500000000000 : ℝ)^3261
        have hw : |(-411752609/2000000000 : ℝ)|=(411752609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209789149/400000000 : ℝ)|^4285 ≤ (42826453123859/100000000000000 : ℝ)^3261
        have hw : |(209789149/400000000 : ℝ)|=(209789149/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412921811/10000000000 : ℝ)|^4285 ≤ (22320070837667/50000000000000 : ℝ)^3261
        have hw : |(5412921811/10000000000 : ℝ)|=(5412921811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305722813/10000000000 : ℝ)*x 0 + (-30879359/156250000 : ℝ)*x 1 + (33830761/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305722813/10000000000 : ℝ)^4285 ≤ (1739283820289/4000000000000 : ℝ)^3261 := by
    have hnat : (5305722813 : ℕ)^4285*4000000000000^3261 ≤ 1739283820289^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305722813 10000000000 1739283820289 4000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30879359/156250000 : ℝ)^4285 ≤ (11877763354717/100000000000000 : ℝ)^3261 := by
    have hnat : (30879359 : ℕ)^4285*100000000000000^3261 ≤ 11877763354717^3261*156250000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30879359 156250000 11877763354717 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33830761/62500000 : ℝ)^4285 ≤ (22320070561333/50000000000000 : ℝ)^3261 := by
    have hnat : (33830761 : ℕ)^4285*50000000000000^3261 ≤ 22320070561333^3261*62500000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33830761 62500000 22320070561333 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305722813/10000000000 : ℝ), (-30879359/156250000 : ℝ), (33830761/62500000 : ℝ)] ![(1739283820289/4000000000000 : ℝ), (11877763354717/100000000000000 : ℝ), (22320070561333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305722813/10000000000 : ℝ)|^4285 ≤ (1739283820289/4000000000000 : ℝ)^3261
        have hw : |(5305722813/10000000000 : ℝ)|=(5305722813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30879359/156250000 : ℝ)|^4285 ≤ (11877763354717/100000000000000 : ℝ)^3261
        have hw : |(-30879359/156250000 : ℝ)|=(30879359/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33830761/62500000 : ℝ)|^4285 ≤ (22320070561333/50000000000000 : ℝ)^3261
        have hw : |(33830761/62500000 : ℝ)|=(33830761/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305722829/10000000000 : ℝ)*x 0 + (5412921719/10000000000 : ℝ)*x 1 + (-197627901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305722829/10000000000 : ℝ)^4285 ≤ (1739283827181/4000000000000 : ℝ)^3261 := by
    have hnat : (5305722829 : ℕ)^4285*4000000000000^3261 ≤ 1739283827181^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305722829 10000000000 1739283827181 4000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412921719/10000000000 : ℝ)^4285 ≤ (8928028135673/20000000000000 : ℝ)^3261 := by
    have hnat : (5412921719 : ℕ)^4285*20000000000000^3261 ≤ 8928028135673^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412921719 10000000000 8928028135673 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197627901/1000000000 : ℝ)^4285 ≤ (1187776362323/10000000000000 : ℝ)^3261 := by
    have hnat : (197627901 : ℕ)^4285*10000000000000^3261 ≤ 1187776362323^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197627901 1000000000 1187776362323 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305722829/10000000000 : ℝ), (5412921719/10000000000 : ℝ), (-197627901/1000000000 : ℝ)] ![(1739283827181/4000000000000 : ℝ), (8928028135673/20000000000000 : ℝ), (1187776362323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305722829/10000000000 : ℝ)|^4285 ≤ (1739283827181/4000000000000 : ℝ)^3261
        have hw : |(5305722829/10000000000 : ℝ)|=(5305722829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412921719/10000000000 : ℝ)|^4285 ≤ (8928028135673/20000000000000 : ℝ)^3261
        have hw : |(5412921719/10000000000 : ℝ)|=(5412921719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197627901/1000000000 : ℝ)|^4285 ≤ (1187776362323/10000000000000 : ℝ)^3261
        have hw : |(-197627901/1000000000 : ℝ)|=(197627901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s7_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541389073/1250000000 : ℝ)*x 0 + (2254744441/5000000000 : ℝ)*x 1 + (415944847/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541389073/1250000000 : ℝ)^4285 ≤ (33303247229033/100000000000000 : ℝ)^3261 := by
    have hnat : (541389073 : ℕ)^4285*100000000000000^3261 ≤ 33303247229033^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541389073 1250000000 33303247229033 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254744441/5000000000 : ℝ)^4285 ≤ (8779270470747/25000000000000 : ℝ)^3261 := by
    have hnat : (2254744441 : ℕ)^4285*25000000000000^3261 ≤ 8779270470747^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254744441 5000000000 8779270470747 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415944847/1000000000 : ℝ)^4285 ≤ (6315934174149/20000000000000 : ℝ)^3261 := by
    have hnat : (415944847 : ℕ)^4285*20000000000000^3261 ≤ 6315934174149^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415944847 1000000000 6315934174149 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541389073/1250000000 : ℝ), (2254744441/5000000000 : ℝ), (415944847/1000000000 : ℝ)] ![(33303247229033/100000000000000 : ℝ), (8779270470747/25000000000000 : ℝ), (6315934174149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541389073/1250000000 : ℝ)|^4285 ≤ (33303247229033/100000000000000 : ℝ)^3261
        have hw : |(541389073/1250000000 : ℝ)|=(541389073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254744441/5000000000 : ℝ)|^4285 ≤ (8779270470747/25000000000000 : ℝ)^3261
        have hw : |(2254744441/5000000000 : ℝ)|=(2254744441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415944847/1000000000 : ℝ)|^4285 ≤ (6315934174149/20000000000000 : ℝ)^3261
        have hw : |(415944847/1000000000 : ℝ)|=(415944847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2777/25000 : ℝ) ^ (1071/256 : ℝ) ≤ (1017016959167683/10000000000000000000 : ℝ) := by
    have hpowers : (2777/25000 : ℝ)^1071 ≤ (1017016959167683/10000000000000000000 : ℝ)^256 := by
      have hnat : (2777 : ℕ)^1071*10000000000000000000^256 ≤ 1017016959167683^256*25000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2777 25000 1017016959167683 10000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2777/25000 : ℝ)) (X := (1017016959167683/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14697/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (16405639879419529/50000000000000000000 : ℝ) := by
    have hpowers : (14697/100000 : ℝ)^1071 ≤ (16405639879419529/50000000000000000000 : ℝ)^256 := by
      have hnat : (14697 : ℕ)^1071*50000000000000000000^256 ≤ 16405639879419529^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14697 100000 16405639879419529 50000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14697/100000 : ℝ)) (X := (16405639879419529/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001017016959167683/5000000000000000000 : ℝ) ≤ (2500121538839609/2500000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (5001017016959167683/5000000000000000000 : ℝ)^256 ≤ (2500121538839609/2500000000000000 : ℝ)^1071 := by
      have hnat : (5001017016959167683 : ℕ)^256*2500000000000000^1071 ≤ 2500121538839609^1071*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001017016959167683 5000000000000000000 2500121538839609 2500000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500121538839609/2500000000000000 : ℝ)) (X := (5001017016959167683/5000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252686340584407243/6250000000000000000 : ℝ) ≤ (10001027213075237/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (6252686340584407243/6250000000000000000 : ℝ)^256 ≤ (10001027213075237/10000000000000000 : ℝ)^1071 := by
      have hnat : (6252686340584407243 : ℕ)^256*10000000000000000^1071 ≤ 10001027213075237^1071*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252686340584407243 6250000000000000000 10001027213075237 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001027213075237/10000000000000000 : ℝ)) (X := (6252686340584407243/6250000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016405639879419529/25000000000000000000 : ℝ) ≤ (5000784135396019/5000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (25016405639879419529/25000000000000000000 : ℝ)^256 ≤ (5000784135396019/5000000000000000 : ℝ)^1071 := by
      have hnat : (25016405639879419529 : ℕ)^256*5000000000000000^1071 ≤ 5000784135396019^1071*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016405639879419529 25000000000000000000 5000784135396019 5000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000784135396019/5000000000000000 : ℝ)) (X := (25016405639879419529/25000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1017016959167683/10000000000000000000 : ℝ) ≤ ((8969931168336243947/8972500000000000000 : ℝ)+2*(541057716801/358900000000000 : ℝ)*(2777/25000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (8969931168336243947/8972500000000000000 : ℝ)+2*(541057716801/358900000000000 : ℝ)*(2777/25000 : ℝ)=(2500121538839609/2500000000000000 : ℝ) by norm_num, show 1+2*(1017016959167683/10000000000000000000 : ℝ)=(5001017016959167683/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16405639879419529/50000000000000000000 : ℝ)+(1017016959167683/10000000000000000000 : ℝ) ≤ ((8969931168336243947/8972500000000000000 : ℝ)+(541057716801/358900000000000 : ℝ)*((14697/100000 : ℝ)+(2777/25000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (8969931168336243947/8972500000000000000 : ℝ)+(541057716801/358900000000000 : ℝ)*((14697/100000 : ℝ)+(2777/25000 : ℝ))=(10001027213075237/10000000000000000 : ℝ) by norm_num, show 1+(16405639879419529/50000000000000000000 : ℝ)+(1017016959167683/10000000000000000000 : ℝ)=(6252686340584407243/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16405639879419529/50000000000000000000 : ℝ) ≤ ((8969931168336243947/8972500000000000000 : ℝ)+2*(541057716801/358900000000000 : ℝ)*(14697/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (8969931168336243947/8972500000000000000 : ℝ)+2*(541057716801/358900000000000 : ℝ)*(14697/100000 : ℝ)=(5000784135396019/5000000000000000 : ℝ) by norm_num, show 1+2*(16405639879419529/50000000000000000000 : ℝ)=(25016405639879419529/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8969931168336243947/8972500000000000000 : ℝ)*(X 1 0+X 2 0)+(541057716801/358900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (8969931168336243947/8972500000000000000 : ℝ)) (alpha := (541057716801/358900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8969931168336243947/8972500000000000000 : ℝ)*(X 0 1+X 2 1)+(541057716801/358900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (8969931168336243947/8972500000000000000 : ℝ)) (alpha := (541057716801/358900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8969931168336243947/8972500000000000000 : ℝ)*(X 0 2+X 1 2)+(541057716801/358900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (8969931168336243947/8972500000000000000 : ℝ)) (alpha := (541057716801/358900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-514687929/2500000000 : ℝ)*X 0 0+(10573303/19531250 : ℝ)*X 0 1+(1048824351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674635123/5000000000 : ℝ)*X 1 0+(-429015529/2000000000 : ℝ)*X 1 1+(655515541/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337317957/2500000000 : ℝ)*X 2 0+(5244122657/10000000000 : ℝ)*X 2 1+(-2145077751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33836607/78125000 : ℝ)*X 0 0+(2079092127/5000000000 : ℝ)*X 0 1+(225537393/500000000 : ℝ)*X 0 2+(33836607/78125000 : ℝ)*X 1 0+(2079092127/5000000000 : ℝ)*X 1 1+(225537393/500000000 : ℝ)*X 1 2+(33836607/78125000 : ℝ)*X 2 0+(2079092127/5000000000 : ℝ)*X 2 1+(225537393/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411752609/2000000000 : ℝ)*X 0 0+(209789149/400000000 : ℝ)*X 0 1+(5412921811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305722813/10000000000 : ℝ)*X 1 0+(-30879359/156250000 : ℝ)*X 1 1+(33830761/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305722829/10000000000 : ℝ)*X 2 0+(5412921719/10000000000 : ℝ)*X 2 1+(-197627901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((541389073/1250000000 : ℝ)*X 0 0+(2254744441/5000000000 : ℝ)*X 0 1+(415944847/1000000000 : ℝ)*X 0 2+(541389073/1250000000 : ℝ)*X 1 0+(2254744441/5000000000 : ℝ)*X 1 1+(415944847/1000000000 : ℝ)*X 1 2+(541389073/1250000000 : ℝ)*X 2 0+(2254744441/5000000000 : ℝ)*X 2 1+(415944847/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1960402828317142709658471267/224312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1585532549/100000000000000 : ℝ)*(base19) + (1026561331/50000000000000 : ℝ)*(base23) + (147794901/100000000000000 : ℝ)*(upper2) + (733619943/100000000000000 : ℝ)*(upper3) + (415764519/50000000000000 : ℝ)*(upper4) + (6991542651919/160000000000 : ℝ)*(major0) + (6991542651919/160000000000 : ℝ)*(major1) + (136553567420293/3125000000000 : ℝ)*(major2) + (1475737393775971/25000000000000 : ℝ)*(sp0) + (2951519589913133/50000000000000 : ℝ)*(sp1) + (5903038712236153/100000000000000 : ℝ)*(sp2) + (1418183215516681/50000000000000 : ℝ)*(sp3) + (91190254931/100000000000000 : ℝ)*(sp4) + (10413593187/50000000000000 : ℝ)*(sp7) + (354548407277467/12500000000000 : ℝ)*(f.failure) + (1180608153071763/20000000000000 : ℝ)*(f.sum) + (63898176929741/35890000000000000000000000000 : ℝ)*base65 + (13287223158802667/1435600000000000000000000000000 : ℝ)*base68 + (46947927283256509/112156250000000000000000000000000 : ℝ)*base69 + (13175965291491067/1435600000000000000000000000000 : ℝ)*base72 + (18500136506611/35890000000000000000000000000 : ℝ)*base73 + (359370064703787759/112156250000000000000000000000000 : ℝ)*base75 + (4530770165791907/1435600000000000000000000000000 : ℝ)*base78 + (27556755200537907/1435600000000000000000000000000 : ℝ)*base80 + (4164717456921/1794500000000000000000000000 : ℝ)*base81 + (451749/78125000000000000000 : ℝ)*base89 + (451749/78125000000000000000 : ℝ)*base91 + (329501/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66940633495443733071381/17945000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250857479/25000000000000 : ℝ)*(base19) + (232899151/20000000000000 : ℝ)*(base23) + (82023847/25000000000000 : ℝ)*(lower1) + (75452007/100000000000000 : ℝ)*(upper2) + (101863571/100000000000000 : ℝ)*(upper3) + (156043239/100000000000000 : ℝ)*(upper5) + (2200582743386607/50000000000000 : ℝ)*(major0) + (2200582743386607/50000000000000 : ℝ)*(major1) + (2200582743386607/50000000000000 : ℝ)*(major2) + (5651313/5000000000000 : ℝ)*(sp2) + (5945528491382527/100000000000000 : ℝ)*(sp4) + (1486381871988153/25000000000000 : ℝ)*(sp5) + (185797725433141/3125000000000 : ℝ)*(sp6) + (357100294727477/12500000000000 : ℝ)*(sp7) + (357100294727477/12500000000000 : ℝ)*(f.failure) + (5945528491382527/100000000000000 : ℝ)*(f.sum) + (116205100612991/17945000000000000000000000000 : ℝ)*base66 + (341795656296917829/448625000000000000000000000000000 : ℝ)*base67 + (3443031009024332171/448625000000000000000000000000000 : ℝ)*base70 + (1308798145622707171/448625000000000000000000000000000 : ℝ)*base72 + (33836877804793/8972500000000000000000000000 : ℝ)*base74 + (1379822903380207171/448625000000000000000000000000000 : ℝ)*base76 + (4958091956463792829/448625000000000000000000000000000 : ℝ)*base77 + (421092425147292829/448625000000000000000000000000000 : ℝ)*base79 + (339146708079443/8972500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (169969/78125000000000000000 : ℝ)*base89 + (169969/78125000000000000000 : ℝ)*base91 + (169969/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s8_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029377251/5000000000 : ℝ)*x 0 + (5413516137/10000000000 : ℝ)*x 1 + (5244134827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029377251/5000000000 : ℝ)^4285 ≤ (2506667369287/20000000000000 : ℝ)^3261 := by
    have hnat : (1029377251 : ℕ)^4285*20000000000000^3261 ≤ 2506667369287^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029377251 5000000000 2506667369287 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413516137/10000000000 : ℝ)^4285 ≤ (44646582271279/100000000000000 : ℝ)^3261 := by
    have hnat : (5413516137 : ℕ)^4285*100000000000000^3261 ≤ 44646582271279^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413516137 10000000000 44646582271279 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244134827/10000000000 : ℝ)^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261 := by
    have hnat : (5244134827 : ℕ)^4285*100000000000000^3261 ≤ 42820080867397^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134827 10000000000 42820080867397 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029377251/5000000000 : ℝ), (5413516137/10000000000 : ℝ), (5244134827/10000000000 : ℝ)] ![(2506667369287/20000000000000 : ℝ), (44646582271279/100000000000000 : ℝ), (42820080867397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029377251/5000000000 : ℝ)|^4285 ≤ (2506667369287/20000000000000 : ℝ)^3261
        have hw : |(-1029377251/5000000000 : ℝ)|=(1029377251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413516137/10000000000 : ℝ)|^4285 ≤ (44646582271279/100000000000000 : ℝ)^3261
        have hw : |(5413516137/10000000000 : ℝ)|=(5413516137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244134827/10000000000 : ℝ)|^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261
        have hw : |(5244134827/10000000000 : ℝ)|=(5244134827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s8_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674633511/5000000000 : ℝ)*x 0 + (-2145068039/10000000000 : ℝ)*x 1 + (5244134827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674633511/5000000000 : ℝ)^4285 ≤ (2746975999911/6250000000000 : ℝ)^3261 := by
    have hnat : (2674633511 : ℕ)^4285*6250000000000^3261 ≤ 2746975999911^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674633511 5000000000 2746975999911 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145068039/10000000000 : ℝ)^4285 ≤ (2645660623419/20000000000000 : ℝ)^3261 := by
    have hnat : (2145068039 : ℕ)^4285*20000000000000^3261 ≤ 2645660623419^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145068039 10000000000 2645660623419 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244134827/10000000000 : ℝ)^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261 := by
    have hnat : (5244134827 : ℕ)^4285*100000000000000^3261 ≤ 42820080867397^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134827 10000000000 42820080867397 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674633511/5000000000 : ℝ), (-2145068039/10000000000 : ℝ), (5244134827/10000000000 : ℝ)] ![(2746975999911/6250000000000 : ℝ), (2645660623419/20000000000000 : ℝ), (42820080867397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674633511/5000000000 : ℝ)|^4285 ≤ (2746975999911/6250000000000 : ℝ)^3261
        have hw : |(2674633511/5000000000 : ℝ)|=(2674633511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145068039/10000000000 : ℝ)|^4285 ≤ (2645660623419/20000000000000 : ℝ)^3261
        have hw : |(-2145068039/10000000000 : ℝ)|=(2145068039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244134827/10000000000 : ℝ)|^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261
        have hw : |(5244134827/10000000000 : ℝ)|=(5244134827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s8_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674633511/5000000000 : ℝ)*x 0 + (5244134827/10000000000 : ℝ)*x 1 + (-2145068039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674633511/5000000000 : ℝ)^4285 ≤ (2746975999911/6250000000000 : ℝ)^3261 := by
    have hnat : (2674633511 : ℕ)^4285*6250000000000^3261 ≤ 2746975999911^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674633511 5000000000 2746975999911 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244134827/10000000000 : ℝ)^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261 := by
    have hnat : (5244134827 : ℕ)^4285*100000000000000^3261 ≤ 42820080867397^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244134827 10000000000 42820080867397 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145068039/10000000000 : ℝ)^4285 ≤ (2645660623419/20000000000000 : ℝ)^3261 := by
    have hnat : (2145068039 : ℕ)^4285*20000000000000^3261 ≤ 2645660623419^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145068039 10000000000 2645660623419 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674633511/5000000000 : ℝ), (5244134827/10000000000 : ℝ), (-2145068039/10000000000 : ℝ)] ![(2746975999911/6250000000000 : ℝ), (42820080867397/100000000000000 : ℝ), (2645660623419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674633511/5000000000 : ℝ)|^4285 ≤ (2746975999911/6250000000000 : ℝ)^3261
        have hw : |(2674633511/5000000000 : ℝ)|=(2674633511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244134827/10000000000 : ℝ)|^4285 ≤ (42820080867397/100000000000000 : ℝ)^3261
        have hw : |(5244134827/10000000000 : ℝ)|=(5244134827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145068039/10000000000 : ℝ)|^4285 ≤ (2645660623419/20000000000000 : ℝ)^3261
        have hw : |(-2145068039/10000000000 : ℝ)|=(2145068039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s8_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331087807/10000000000 : ℝ)*x 0 + (4158208567/10000000000 : ℝ)*x 1 + (1127680519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331087807/10000000000 : ℝ)^4285 ≤ (1332119875441/4000000000000 : ℝ)^3261 := by
    have hnat : (4331087807 : ℕ)^4285*4000000000000^3261 ≤ 1332119875441^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331087807 10000000000 1332119875441 4000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158208567/10000000000 : ℝ)^4285 ≤ (3156730173769/10000000000000 : ℝ)^3261 := by
    have hnat : (4158208567 : ℕ)^4285*10000000000000^3261 ≤ 3156730173769^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158208567 10000000000 3156730173769 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127680519/2500000000 : ℝ)^4285 ≤ (35129701354733/100000000000000 : ℝ)^3261 := by
    have hnat : (1127680519 : ℕ)^4285*100000000000000^3261 ≤ 35129701354733^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127680519 2500000000 35129701354733 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331087807/10000000000 : ℝ), (4158208567/10000000000 : ℝ), (1127680519/2500000000 : ℝ)] ![(1332119875441/4000000000000 : ℝ), (3156730173769/10000000000000 : ℝ), (35129701354733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331087807/10000000000 : ℝ)|^4285 ≤ (1332119875441/4000000000000 : ℝ)^3261
        have hw : |(4331087807/10000000000 : ℝ)|=(4331087807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158208567/10000000000 : ℝ)|^4285 ≤ (3156730173769/10000000000000 : ℝ)^3261
        have hw : |(4158208567/10000000000 : ℝ)|=(4158208567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127680519/2500000000 : ℝ)|^4285 ≤ (35129701354733/100000000000000 : ℝ)^3261
        have hw : |(1127680519/2500000000 : ℝ)|=(1127680519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s8_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-514691879/2500000000 : ℝ)*x 0 + (1311184871/2500000000 : ℝ)*x 1 + (2706453929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514691879/2500000000 : ℝ)^4285 ≤ (195835014873/1562500000000 : ℝ)^3261 := by
    have hnat : (514691879 : ℕ)^4285*1562500000000^3261 ≤ 195835014873^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514691879 2500000000 195835014873 1562500000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311184871/2500000000 : ℝ)^4285 ≤ (5353321070643/12500000000000 : ℝ)^3261 := by
    have hnat : (1311184871 : ℕ)^4285*12500000000000^3261 ≤ 5353321070643^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311184871 2500000000 5353321070643 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706453929/5000000000 : ℝ)^4285 ≤ (44639990472039/100000000000000 : ℝ)^3261 := by
    have hnat : (2706453929 : ℕ)^4285*100000000000000^3261 ≤ 44639990472039^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706453929 5000000000 44639990472039 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514691879/2500000000 : ℝ), (1311184871/2500000000 : ℝ), (2706453929/5000000000 : ℝ)] ![(195835014873/1562500000000 : ℝ), (5353321070643/12500000000000 : ℝ), (44639990472039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514691879/2500000000 : ℝ)|^4285 ≤ (195835014873/1562500000000 : ℝ)^3261
        have hw : |(-514691879/2500000000 : ℝ)|=(514691879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311184871/2500000000 : ℝ)|^4285 ≤ (5353321070643/12500000000000 : ℝ)^3261
        have hw : |(1311184871/2500000000 : ℝ)|=(1311184871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706453929/5000000000 : ℝ)|^4285 ≤ (44639990472039/100000000000000 : ℝ)^3261
        have hw : |(2706453929/5000000000 : ℝ)|=(2706453929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s8_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331114287/10000000000 : ℝ)*x 0 + (4509461667/10000000000 : ℝ)*x 1 + (207973733/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331114287/10000000000 : ℝ)^4285 ≤ (33303264435901/100000000000000 : ℝ)^3261 := by
    have hnat : (4331114287 : ℕ)^4285*100000000000000^3261 ≤ 33303264435901^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331114287 10000000000 33303264435901 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509461667/10000000000 : ℝ)^4285 ≤ (35116803399753/100000000000000 : ℝ)^3261 := by
    have hnat : (4509461667 : ℕ)^4285*100000000000000^3261 ≤ 35116803399753^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509461667 10000000000 35116803399753 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207973733/500000000 : ℝ)^4285 ≤ (31579932151731/100000000000000 : ℝ)^3261 := by
    have hnat : (207973733 : ℕ)^4285*100000000000000^3261 ≤ 31579932151731^3261*500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207973733 500000000 31579932151731 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331114287/10000000000 : ℝ), (4509461667/10000000000 : ℝ), (207973733/500000000 : ℝ)] ![(33303264435901/100000000000000 : ℝ), (35116803399753/100000000000000 : ℝ), (31579932151731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331114287/10000000000 : ℝ)|^4285 ≤ (33303264435901/100000000000000 : ℝ)^3261
        have hw : |(4331114287/10000000000 : ℝ)|=(4331114287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509461667/10000000000 : ℝ)|^4285 ≤ (35116803399753/100000000000000 : ℝ)^3261
        have hw : |(4509461667/10000000000 : ℝ)|=(4509461667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207973733/500000000 : ℝ)|^4285 ≤ (31579932151731/100000000000000 : ℝ)^3261
        have hw : |(207973733/500000000 : ℝ)|=(207973733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1111/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11109/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (10174000520334211/100000000000000000000 : ℝ) := by
    have hpowers : (11109/100000 : ℝ)^1071 ≤ (10174000520334211/100000000000000000000 : ℝ)^256 := by
      have hnat : (11109 : ℕ)^1071*100000000000000000000^256 ≤ 10174000520334211^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11109 100000 10174000520334211 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11109/100000 : ℝ)) (X := (10174000520334211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2939/20000 : ℝ) ^ (1071/256 : ℝ) ≤ (8198150982327093/25000000000000000000 : ℝ) := by
    have hpowers : (2939/20000 : ℝ)^1071 ≤ (8198150982327093/25000000000000000000 : ℝ)^256 := by
      have hnat : (2939 : ℕ)^1071*25000000000000000000^256 ≤ 8198150982327093^256*20000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2939 20000 8198150982327093 25000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2939/20000 : ℝ)) (X := (8198150982327093/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010174000520334211/50000000000000000000 : ℝ) ≤ (2000097267694131/2000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50010174000520334211/50000000000000000000 : ℝ)^256 ≤ (2000097267694131/2000000000000000 : ℝ)^1071 := by
      have hnat : (50010174000520334211 : ℕ)^256*2000000000000000^1071 ≤ 2000097267694131^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010174000520334211 50000000000000000000 2000097267694131 2000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097267694131/2000000000000000 : ℝ)) (X := (50010174000520334211/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042966604449642583/100000000000000000000 : ℝ) ≤ (10001026858355133/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (100042966604449642583/100000000000000000000 : ℝ)^256 ≤ (10001026858355133/10000000000000000 : ℝ)^1071 := by
      have hnat : (100042966604449642583 : ℕ)^256*10000000000000000^1071 ≤ 10001026858355133^1071*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042966604449642583 100000000000000000000 10001026858355133 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001026858355133/10000000000000000 : ℝ)) (X := (100042966604449642583/100000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508198150982327093/12500000000000000000 : ℝ) ≤ (10001567378239611/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (12508198150982327093/12500000000000000000 : ℝ)^256 ≤ (10001567378239611/10000000000000000 : ℝ)^1071 := by
      have hnat : (12508198150982327093 : ℕ)^256*10000000000000000^1071 ≤ 10001567378239611^1071*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508198150982327093 12500000000000000000 10001567378239611 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001567378239611/10000000000000000 : ℝ)) (X := (12508198150982327093/12500000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10174000520334211/100000000000000000000 : ℝ) ≤ ((17924867369481218313/17930000000000000000 : ℝ)+2*(270259942239/179300000000000 : ℝ)*(11109/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (17924867369481218313/17930000000000000000 : ℝ)+2*(270259942239/179300000000000 : ℝ)*(11109/100000 : ℝ)=(2000097267694131/2000000000000000 : ℝ) by norm_num, show 1+2*(10174000520334211/100000000000000000000 : ℝ)=(50010174000520334211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8198150982327093/25000000000000000000 : ℝ)+(10174000520334211/100000000000000000000 : ℝ) ≤ ((17924867369481218313/17930000000000000000 : ℝ)+(270259942239/179300000000000 : ℝ)*((2939/20000 : ℝ)+(11109/100000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (17924867369481218313/17930000000000000000 : ℝ)+(270259942239/179300000000000 : ℝ)*((2939/20000 : ℝ)+(11109/100000 : ℝ))=(10001026858355133/10000000000000000 : ℝ) by norm_num, show 1+(8198150982327093/25000000000000000000 : ℝ)+(10174000520334211/100000000000000000000 : ℝ)=(100042966604449642583/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8198150982327093/25000000000000000000 : ℝ) ≤ ((17924867369481218313/17930000000000000000 : ℝ)+2*(270259942239/179300000000000 : ℝ)*(2939/20000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (17924867369481218313/17930000000000000000 : ℝ)+2*(270259942239/179300000000000 : ℝ)*(2939/20000 : ℝ)=(10001567378239611/10000000000000000 : ℝ) by norm_num, show 1+2*(8198150982327093/25000000000000000000 : ℝ)=(12508198150982327093/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17924867369481218313/17930000000000000000 : ℝ)*(X 1 0+X 2 0)+(270259942239/179300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17924867369481218313/17930000000000000000 : ℝ)) (alpha := (270259942239/179300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17924867369481218313/17930000000000000000 : ℝ)*(X 0 1+X 2 1)+(270259942239/179300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17924867369481218313/17930000000000000000 : ℝ)) (alpha := (270259942239/179300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17924867369481218313/17930000000000000000 : ℝ)*(X 0 2+X 1 2)+(270259942239/179300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (17924867369481218313/17930000000000000000 : ℝ)) (alpha := (270259942239/179300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1029377251/5000000000 : ℝ)*X 0 0+(5413516137/10000000000 : ℝ)*X 0 1+(5244134827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674633511/5000000000 : ℝ)*X 1 0+(-2145068039/10000000000 : ℝ)*X 1 1+(5244134827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674633511/5000000000 : ℝ)*X 2 0+(5244134827/10000000000 : ℝ)*X 2 1+(-2145068039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331087807/10000000000 : ℝ)*X 0 0+(4158208567/10000000000 : ℝ)*X 0 1+(1127680519/2500000000 : ℝ)*X 0 2+(4331087807/10000000000 : ℝ)*X 1 0+(4158208567/10000000000 : ℝ)*X 1 1+(1127680519/2500000000 : ℝ)*X 1 2+(4331087807/10000000000 : ℝ)*X 2 0+(4158208567/10000000000 : ℝ)*X 2 1+(1127680519/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-514691879/2500000000 : ℝ)*X 0 0+(1311184871/2500000000 : ℝ)*X 0 1+(2706453929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4331114287/10000000000 : ℝ)*X 0 0+(4509461667/10000000000 : ℝ)*X 0 1+(207973733/500000000 : ℝ)*X 0 2+(4331114287/10000000000 : ℝ)*X 1 0+(4509461667/10000000000 : ℝ)*X 1 1+(207973733/500000000 : ℝ)*X 1 2+(4331114287/10000000000 : ℝ)*X 2 0+(4509461667/10000000000 : ℝ)*X 2 1+(207973733/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (994424626195818883598421939/448250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422894441/100000000000000 : ℝ)*(base19) + (393833643/100000000000000 : ℝ)*(base23) + (15545397/100000000000000 : ℝ)*(lower2) + (3516951/6250000000000 : ℝ)*(upper3) + (34786283/100000000000000 : ℝ)*(upper5) + (2185158977346999/50000000000000 : ℝ)*(major0) + (2185158977346999/50000000000000 : ℝ)*(major1) + (2185158977346999/50000000000000 : ℝ)*(major2) + (36899050431219/625000000000 : ℝ)*(sp0) + (295192811436621/5000000000000 : ℝ)*(sp1) + (5903856257793219/100000000000000 : ℝ)*(sp2) + (1418387359270273/50000000000000 : ℝ)*(sp3) + (8582631821/100000000000000 : ℝ)*(sp4) + (893054383/20000000000000 : ℝ)*(sp5) + (141838959190623/5000000000000 : ℝ)*(f.failure) + (2951928325813431/50000000000000 : ℝ)*(f.sum) + (48667000974593/8965000000000000000000000000 : ℝ)*base66 + (1699092772808992687/896500000000000000000000000000000 : ℝ)*base67 + (5018340634320507313/896500000000000000000000000000000 : ℝ)*base70 + (7633649576984992687/896500000000000000000000000000000 : ℝ)*base71 + (12622680538733/8965000000000000000000000000 : ℝ)*base74 + (2705356148673507313/896500000000000000000000000000000 : ℝ)*base76 + (4295378903807992687/896500000000000000000000000000000 : ℝ)*base77 + (16692286731150492687/896500000000000000000000000000000 : ℝ)*base79 + (22793691318553/8965000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (266769/31250000000000000000 : ℝ)*base90 + (266769/31250000000000000000 : ℝ)*base92 + (266769/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1325_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1325_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1325_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1325_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1325_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1111/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
