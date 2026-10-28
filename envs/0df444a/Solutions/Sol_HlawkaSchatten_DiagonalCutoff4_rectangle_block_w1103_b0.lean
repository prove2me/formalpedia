-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:19.776137+00:00
-- url     : https://prove2.me/submissions/04e7d810-0c2f-4349-9ae6-008b04410063

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
theorem support_rectangle_w1103_s0_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-952107727/5000000000 : ℝ)*x 0 + (6063388049/10000000000 : ℝ)*x 1 + (4775520423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952107727/5000000000 : ℝ)^1037 ≤ (11056505871467/100000000000000 : ℝ)^781 := by
    have hnat : (952107727 : ℕ)^1037*100000000000000^781 ≤ 11056505871467^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952107727 5000000000 11056505871467 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6063388049/10000000000 : ℝ)^1037 ≤ (2058508827783/4000000000000 : ℝ)^781 := by
    have hnat : (6063388049 : ℕ)^1037*4000000000000^781 ≤ 2058508827783^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6063388049 10000000000 2058508827783 4000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775520423/10000000000 : ℝ)^1037 ≤ (149923093669/400000000000 : ℝ)^781 := by
    have hnat : (4775520423 : ℕ)^1037*400000000000^781 ≤ 149923093669^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775520423 10000000000 149923093669 400000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952107727/5000000000 : ℝ), (6063388049/10000000000 : ℝ), (4775520423/10000000000 : ℝ)] ![(11056505871467/100000000000000 : ℝ), (2058508827783/4000000000000 : ℝ), (149923093669/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952107727/5000000000 : ℝ)|^1037 ≤ (11056505871467/100000000000000 : ℝ)^781
        have hw : |(-952107727/5000000000 : ℝ)|=(952107727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6063388049/10000000000 : ℝ)|^1037 ≤ (2058508827783/4000000000000 : ℝ)^781
        have hw : |(6063388049/10000000000 : ℝ)|=(6063388049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775520423/10000000000 : ℝ)|^1037 ≤ (149923093669/400000000000 : ℝ)^781
        have hw : |(4775520423/10000000000 : ℝ)|=(4775520423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2759495289/5000000000 : ℝ)*x 0 + (-528886631/2000000000 : ℝ)*x 1 + (4775519623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759495289/5000000000 : ℝ)^1037 ≤ (9083958524227/20000000000000 : ℝ)^781 := by
    have hnat : (2759495289 : ℕ)^1037*20000000000000^781 ≤ 9083958524227^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759495289 5000000000 9083958524227 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528886631/2000000000 : ℝ)^1037 ≤ (17099442282021/100000000000000 : ℝ)^781 := by
    have hnat : (528886631 : ℕ)^1037*100000000000000^781 ≤ 17099442282021^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528886631 2000000000 17099442282021 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775519623/10000000000 : ℝ)^1037 ≤ (9370191270083/25000000000000 : ℝ)^781 := by
    have hnat : (4775519623 : ℕ)^1037*25000000000000^781 ≤ 9370191270083^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775519623 10000000000 9370191270083 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759495289/5000000000 : ℝ), (-528886631/2000000000 : ℝ), (4775519623/10000000000 : ℝ)] ![(9083958524227/20000000000000 : ℝ), (17099442282021/100000000000000 : ℝ), (9370191270083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759495289/5000000000 : ℝ)|^1037 ≤ (9083958524227/20000000000000 : ℝ)^781
        have hw : |(2759495289/5000000000 : ℝ)|=(2759495289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528886631/2000000000 : ℝ)|^1037 ≤ (17099442282021/100000000000000 : ℝ)^781
        have hw : |(-528886631/2000000000 : ℝ)|=(528886631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775519623/10000000000 : ℝ)|^1037 ≤ (9370191270083/25000000000000 : ℝ)^781
        have hw : |(4775519623/10000000000 : ℝ)|=(4775519623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1379747701/2500000000 : ℝ)*x 0 + (4775519991/10000000000 : ℝ)*x 1 + (-1322216211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379747701/2500000000 : ℝ)^1037 ≤ (22709897545353/50000000000000 : ℝ)^781 := by
    have hnat : (1379747701 : ℕ)^1037*50000000000000^781 ≤ 22709897545353^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379747701 2500000000 22709897545353 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4775519991/10000000000 : ℝ)^1037 ≤ (18740384457657/50000000000000 : ℝ)^781 := by
    have hnat : (4775519991 : ℕ)^1037*50000000000000^781 ≤ 18740384457657^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775519991 10000000000 18740384457657 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322216211/5000000000 : ℝ)^1037 ≤ (17099435988683/100000000000000 : ℝ)^781 := by
    have hnat : (1322216211 : ℕ)^1037*100000000000000^781 ≤ 17099435988683^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322216211 5000000000 17099435988683 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379747701/2500000000 : ℝ), (4775519991/10000000000 : ℝ), (-1322216211/5000000000 : ℝ)] ![(22709897545353/50000000000000 : ℝ), (18740384457657/50000000000000 : ℝ), (17099435988683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379747701/2500000000 : ℝ)|^1037 ≤ (22709897545353/50000000000000 : ℝ)^781
        have hw : |(1379747701/2500000000 : ℝ)|=(1379747701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4775519991/10000000000 : ℝ)|^1037 ≤ (18740384457657/50000000000000 : ℝ)^781
        have hw : |(4775519991/10000000000 : ℝ)|=(4775519991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322216211/5000000000 : ℝ)|^1037 ≤ (17099435988683/100000000000000 : ℝ)^781
        have hw : |(-1322216211/5000000000 : ℝ)|=(1322216211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4204164001/10000000000 : ℝ)*x 0 + (780738691/2500000000 : ℝ)*x 1 + (2832775029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204164001/10000000000 : ℝ)^1037 ≤ (31646633966877/100000000000000 : ℝ)^781 := by
    have hnat : (4204164001 : ℕ)^1037*100000000000000^781 ≤ 31646633966877^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204164001 10000000000 31646633966877 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780738691/2500000000 : ℝ)^1037 ≤ (21325143603079/100000000000000 : ℝ)^781 := by
    have hnat : (780738691 : ℕ)^1037*100000000000000^781 ≤ 21325143603079^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780738691 2500000000 21325143603079 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2832775029/5000000000 : ℝ)^1037 ≤ (5878527802473/12500000000000 : ℝ)^781 := by
    have hnat : (2832775029 : ℕ)^1037*12500000000000^781 ≤ 5878527802473^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832775029 5000000000 5878527802473 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204164001/10000000000 : ℝ), (780738691/2500000000 : ℝ), (2832775029/5000000000 : ℝ)] ![(31646633966877/100000000000000 : ℝ), (21325143603079/100000000000000 : ℝ), (5878527802473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204164001/10000000000 : ℝ)|^1037 ≤ (31646633966877/100000000000000 : ℝ)^781
        have hw : |(4204164001/10000000000 : ℝ)|=(4204164001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(780738691/2500000000 : ℝ)|^1037 ≤ (21325143603079/100000000000000 : ℝ)^781
        have hw : |(780738691/2500000000 : ℝ)|=(780738691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2832775029/5000000000 : ℝ)|^1037 ≤ (5878527802473/12500000000000 : ℝ)^781
        have hw : |(2832775029/5000000000 : ℝ)|=(2832775029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-954739043/5000000000 : ℝ)*x 0 + (240438061/500000000 : ℝ)*x 1 + (1507245179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954739043/5000000000 : ℝ)^1037 ≤ (2774274202327/25000000000000 : ℝ)^781 := by
    have hnat : (954739043 : ℕ)^1037*25000000000000^781 ≤ 2774274202327^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954739043 5000000000 2774274202327 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240438061/500000000 : ℝ)^1037 ≤ (37827575246239/100000000000000 : ℝ)^781 := by
    have hnat : (240438061 : ℕ)^1037*100000000000000^781 ≤ 37827575246239^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240438061 500000000 37827575246239 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507245179/2500000000 : ℝ)^1037 ≤ (51075327930651/100000000000000 : ℝ)^781 := by
    have hnat : (1507245179 : ℕ)^1037*100000000000000^781 ≤ 51075327930651^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507245179 2500000000 51075327930651 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954739043/5000000000 : ℝ), (240438061/500000000 : ℝ), (1507245179/2500000000 : ℝ)] ![(2774274202327/25000000000000 : ℝ), (37827575246239/100000000000000 : ℝ), (51075327930651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954739043/5000000000 : ℝ)|^1037 ≤ (2774274202327/25000000000000 : ℝ)^781
        have hw : |(-954739043/5000000000 : ℝ)|=(954739043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240438061/500000000 : ℝ)|^1037 ≤ (37827575246239/100000000000000 : ℝ)^781
        have hw : |(240438061/500000000 : ℝ)|=(240438061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1507245179/2500000000 : ℝ)|^1037 ≤ (51075327930651/100000000000000 : ℝ)^781
        have hw : |(1507245179/2500000000 : ℝ)|=(1507245179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5169244373/10000000000 : ℝ)*x 0 + (-347743417/2500000000 : ℝ)*x 1 + (6028981797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169244373/10000000000 : ℝ)^1037 ≤ (20819140173239/50000000000000 : ℝ)^781 := by
    have hnat : (5169244373 : ℕ)^1037*50000000000000^781 ≤ 20819140173239^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169244373 10000000000 20819140173239 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347743417/2500000000 : ℝ)^1037 ≤ (7286379554273/100000000000000 : ℝ)^781 := by
    have hnat : (347743417 : ℕ)^1037*100000000000000^781 ≤ 7286379554273^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347743417 2500000000 7286379554273 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6028981797/10000000000 : ℝ)^1037 ≤ (5107534009029/10000000000000 : ℝ)^781 := by
    have hnat : (6028981797 : ℕ)^1037*10000000000000^781 ≤ 5107534009029^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6028981797 10000000000 5107534009029 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169244373/10000000000 : ℝ), (-347743417/2500000000 : ℝ), (6028981797/10000000000 : ℝ)] ![(20819140173239/50000000000000 : ℝ), (7286379554273/100000000000000 : ℝ), (5107534009029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169244373/10000000000 : ℝ)|^1037 ≤ (20819140173239/50000000000000 : ℝ)^781
        have hw : |(5169244373/10000000000 : ℝ)|=(5169244373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347743417/2500000000 : ℝ)|^1037 ≤ (7286379554273/100000000000000 : ℝ)^781
        have hw : |(-347743417/2500000000 : ℝ)|=(347743417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6028981797/10000000000 : ℝ)|^1037 ≤ (5107534009029/10000000000000 : ℝ)^781
        have hw : |(6028981797/10000000000 : ℝ)|=(6028981797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2584623073/5000000000 : ℝ)*x 0 + (6028981181/10000000000 : ℝ)*x 1 + (-1390971937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584623073/5000000000 : ℝ)^1037 ≤ (20819149654633/50000000000000 : ℝ)^781 := by
    have hnat : (2584623073 : ℕ)^1037*50000000000000^781 ≤ 20819149654633^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584623073 5000000000 20819149654633 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6028981181/10000000000 : ℝ)^1037 ≤ (6384416645151/12500000000000 : ℝ)^781 := by
    have hnat : (6028981181 : ℕ)^1037*12500000000000^781 ≤ 6384416645151^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6028981181 10000000000 6384416645151 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390971937/10000000000 : ℝ)^1037 ≤ (182159187863/2500000000000 : ℝ)^781 := by
    have hnat : (1390971937 : ℕ)^1037*2500000000000^781 ≤ 182159187863^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390971937 10000000000 182159187863 2500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584623073/5000000000 : ℝ), (6028981181/10000000000 : ℝ), (-1390971937/10000000000 : ℝ)] ![(20819149654633/50000000000000 : ℝ), (6384416645151/12500000000000 : ℝ), (182159187863/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584623073/5000000000 : ℝ)|^1037 ≤ (20819149654633/50000000000000 : ℝ)^781
        have hw : |(2584623073/5000000000 : ℝ)|=(2584623073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6028981181/10000000000 : ℝ)|^1037 ≤ (6384416645151/12500000000000 : ℝ)^781
        have hw : |(6028981181/10000000000 : ℝ)|=(6028981181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1390971937/10000000000 : ℝ)|^1037 ≤ (182159187863/2500000000000 : ℝ)^781
        have hw : |(-1390971937/10000000000 : ℝ)|=(1390971937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s0_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1053637479/2500000000 : ℝ)*x 0 + (2799962301/5000000000 : ℝ)*x 1 + (797720639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053637479/2500000000 : ℝ)^1037 ≤ (31750481471363/100000000000000 : ℝ)^781 := by
    have hnat : (1053637479 : ℕ)^1037*100000000000000^781 ≤ 31750481471363^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053637479 2500000000 31750481471363 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2799962301/5000000000 : ℝ)^1037 ≤ (23153151160013/50000000000000 : ℝ)^781 := by
    have hnat : (2799962301 : ℕ)^1037*50000000000000^781 ≤ 23153151160013^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799962301 5000000000 23153151160013 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797720639/2500000000 : ℝ)^1037 ≤ (21943216187153/100000000000000 : ℝ)^781 := by
    have hnat : (797720639 : ℕ)^1037*100000000000000^781 ≤ 21943216187153^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797720639 2500000000 21943216187153 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053637479/2500000000 : ℝ), (2799962301/5000000000 : ℝ), (797720639/2500000000 : ℝ)] ![(31750481471363/100000000000000 : ℝ), (23153151160013/50000000000000 : ℝ), (21943216187153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053637479/2500000000 : ℝ)|^1037 ≤ (31750481471363/100000000000000 : ℝ)^781
        have hw : |(1053637479/2500000000 : ℝ)|=(1053637479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2799962301/5000000000 : ℝ)|^1037 ≤ (23153151160013/50000000000000 : ℝ)^781
        have hw : |(2799962301/5000000000 : ℝ)|=(2799962301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(797720639/2500000000 : ℝ)|^1037 ≤ (21943216187153/100000000000000 : ℝ)^781
        have hw : |(797720639/2500000000 : ℝ)|=(797720639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (63/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5593/20000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  have hpowlo : (0 : ℝ) ^ (8295/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8295 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8295*1^2048 ≤ 0^2048*1^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8295/2048 : ℝ) ≤ (2444704550410552009/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8295 ≤ (2444704550410552009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8295*100000000000000000000^2048 ≤ 2444704550410552009^2048*5^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2444704550410552009 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2444704550410552009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8295 := by
      have hnat : (1 : ℕ)^2048*1^8295 ≤ 1^8295*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102444704550410552009/100000000000000000000 : ℝ) ≤ (10059810878442411/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (102444704550410552009/100000000000000000000 : ℝ)^2048 ≤ (10059810878442411/10000000000000000 : ℝ)^8295 := by
      have hnat : (102444704550410552009 : ℕ)^2048*10000000000000000^8295 ≤ 10059810878442411^8295*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102444704550410552009 100000000000000000000 10059810878442411 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059810878442411/10000000000000000 : ℝ)) (X := (102444704550410552009/100000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52444704550410552009/50000000000000000000 : ℝ) ≤ (5059810878442411/5000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (52444704550410552009/50000000000000000000 : ℝ)^2048 ≤ (5059810878442411/5000000000000000 : ℝ)^8295 := by
      have hnat : (52444704550410552009 : ℕ)^2048*5000000000000000^8295 ≤ 5059810878442411^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52444704550410552009 50000000000000000000 5059810878442411 5000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059810878442411/5000000000000000 : ℝ)) (X := (52444704550410552009/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59810878442411/4000000000000000 : ℝ)*(0 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59810878442411/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2444704550410552009/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59810878442411/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (1 : ℝ)+(59810878442411/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059810878442411/10000000000000000 : ℝ) by norm_num, show 1+(2444704550410552009/100000000000000000000 : ℝ)+(0 : ℝ)=(102444704550410552009/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2444704550410552009/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59810878442411/4000000000000000 : ℝ)*(2/5 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59810878442411/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059810878442411/5000000000000000 : ℝ) by norm_num, show 1+2*(2444704550410552009/100000000000000000000 : ℝ)=(52444704550410552009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59810878442411/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59810878442411/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59810878442411/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59810878442411/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59810878442411/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59810878442411/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-952107727/5000000000 : ℝ)*X 0 0+(6063388049/10000000000 : ℝ)*X 0 1+(4775520423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2759495289/5000000000 : ℝ)*X 1 0+(-528886631/2000000000 : ℝ)*X 1 1+(4775519623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379747701/2500000000 : ℝ)*X 2 0+(4775519991/10000000000 : ℝ)*X 2 1+(-1322216211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204164001/10000000000 : ℝ)*X 0 0+(780738691/2500000000 : ℝ)*X 0 1+(2832775029/5000000000 : ℝ)*X 0 2+(4204164001/10000000000 : ℝ)*X 1 0+(780738691/2500000000 : ℝ)*X 1 1+(2832775029/5000000000 : ℝ)*X 1 2+(4204164001/10000000000 : ℝ)*X 2 0+(780738691/2500000000 : ℝ)*X 2 1+(2832775029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-954739043/5000000000 : ℝ)*X 0 0+(240438061/500000000 : ℝ)*X 0 1+(1507245179/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169244373/10000000000 : ℝ)*X 1 0+(-347743417/2500000000 : ℝ)*X 1 1+(6028981797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584623073/5000000000 : ℝ)*X 2 0+(6028981181/10000000000 : ℝ)*X 2 1+(-1390971937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053637479/2500000000 : ℝ)*X 0 0+(2799962301/5000000000 : ℝ)*X 0 1+(797720639/2500000000 : ℝ)*X 0 2+(1053637479/2500000000 : ℝ)*X 1 0+(2799962301/5000000000 : ℝ)*X 1 1+(797720639/2500000000 : ℝ)*X 1 2+(1053637479/2500000000 : ℝ)*X 2 0+(2799962301/5000000000 : ℝ)*X 2 1+(797720639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178943120705561182571049/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89123559/100000000000000 : ℝ)*(base1) + (466966117/50000000000000 : ℝ)*(base19) + (429662601/50000000000000 : ℝ)*(base23) + (10640353/10000000000000 : ℝ)*(base24) + (170493627/100000000000000 : ℝ)*(upper3) + (146222836803047/25000000000000 : ℝ)*(major0) + (146222836803047/25000000000000 : ℝ)*(major1) + (146222836803047/25000000000000 : ℝ)*(major2) + (388239887288737/50000000000000 : ℝ)*(sp0) + (388240224442643/50000000000000 : ℝ)*(sp1) + (776480417088787/100000000000000 : ℝ)*(sp2) + (98324931050633/25000000000000 : ℝ)*(sp3) + (424340901/25000000000000 : ℝ)*(sp4) + (344746337/25000000000000 : ℝ)*(sp7) + (393301192311439/100000000000000 : ℝ)*(f.failure) + (776481382817519/100000000000000 : ℝ)*(f.sum) + (149447330826317/50000000000000000000000000000 : ℝ)*base65 + (104785766173683/100000000000000000000000000000 : ℝ)*base68 + (547216692173683/100000000000000000000000000000 : ℝ)*base70 + (462693521973683/100000000000000000000000000000 : ℝ)*base72 + (226451308126317/50000000000000000000000000000 : ℝ)*base73 + (740212213373683/100000000000000000000000000000 : ℝ)*base76 + (49461465973683/100000000000000000000000000000 : ℝ)*base78 + (364254652726317/100000000000000000000000000000 : ℝ)*base79 + (50913927326317/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (740431/5000000000000000000000 : ℝ)*base90 + (740431/5000000000000000000000 : ℝ)*base92 + (740431/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (513513661527056697920427/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35054121/25000000000000 : ℝ)*(base13) + (17911531/2500000000000 : ℝ)*(base23) + (52750969/12500000000000 : ℝ)*(base39) + (27883217/100000000000000 : ℝ)*(base45) + (1005373/20000000000000 : ℝ)*(upper3) + (50405013/20000000000000 : ℝ)*(upper5) + (617312285998771/100000000000000 : ℝ)*(major0) + (617312285998771/100000000000000 : ℝ)*(major1) + (617311863991019/100000000000000 : ℝ)*(major2) + (377966723/100000000000000 : ℝ)*(sp2) + (102440221267461/12500000000000 : ℝ)*(sp4) + (204880477589043/25000000000000 : ℝ)*(sp5) + (409760618967981/50000000000000 : ℝ)*(sp6) + (207551077024001/50000000000000 : ℝ)*(sp7) + (207551077024001/50000000000000 : ℝ)*(f.failure) + (204880583090981/25000000000000 : ℝ)*(f.sum) + (66191951261631/40000000000000000000000000000 : ℝ)*base66 + (1380853012893191/400000000000000000000000000000 : ℝ)*base68 + (167508052276881/400000000000000000000000000000 : ℝ)*base69 + (2380790382493191/400000000000000000000000000000 : ℝ)*base72 + (92157022978369/40000000000000000000000000000 : ℝ)*base73 + (1111029738123119/400000000000000000000000000000 : ℝ)*base76 + (2616762290123119/400000000000000000000000000000 : ℝ)*base78 + (4689462387323119/400000000000000000000000000000 : ℝ)*base80 + (409179617876881/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26460671/2500000000000000000000 : ℝ)*base89 + (26460671/2500000000000000000000 : ℝ)*base91 + (26460671/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1103_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5593/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1103_s1_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-131981039/625000000 : ℝ)*x 0 + (2856026951/5000000000 : ℝ)*x 1 + (62425083/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131981039/625000000 : ℝ)^1037 ≤ (6341995770703/50000000000000 : ℝ)^781 := by
    have hnat : (131981039 : ℕ)^1037*50000000000000^781 ≤ 6341995770703^781*625000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131981039 625000000 6341995770703 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2856026951/5000000000 : ℝ)^1037 ≤ (47541456910289/100000000000000 : ℝ)^781 := by
    have hnat : (2856026951 : ℕ)^1037*100000000000000^781 ≤ 47541456910289^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856026951 5000000000 47541456910289 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62425083/125000000 : ℝ)^1037 ≤ (19887275766493/50000000000000 : ℝ)^781 := by
    have hnat : (62425083 : ℕ)^1037*50000000000000^781 ≤ 19887275766493^781*125000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62425083 125000000 19887275766493 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131981039/625000000 : ℝ), (2856026951/5000000000 : ℝ), (62425083/125000000 : ℝ)] ![(6341995770703/50000000000000 : ℝ), (47541456910289/100000000000000 : ℝ), (19887275766493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131981039/625000000 : ℝ)|^1037 ≤ (6341995770703/50000000000000 : ℝ)^781
        have hw : |(-131981039/625000000 : ℝ)|=(131981039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2856026951/5000000000 : ℝ)|^1037 ≤ (47541456910289/100000000000000 : ℝ)^781
        have hw : |(2856026951/5000000000 : ℝ)|=(2856026951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62425083/125000000 : ℝ)|^1037 ≤ (19887275766493/50000000000000 : ℝ)^781
        have hw : |(62425083/125000000 : ℝ)|=(62425083/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1355316781/2500000000 : ℝ)*x 0 + (-2499973897/10000000000 : ℝ)*x 1 + (4994006721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355316781/2500000000 : ℝ)^1037 ≤ (44355049565979/100000000000000 : ℝ)^781 := by
    have hnat : (1355316781 : ℕ)^1037*100000000000000^781 ≤ 44355049565979^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355316781 2500000000 44355049565979 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499973897/10000000000 : ℝ)^1037 ≤ (15870398029469/100000000000000 : ℝ)^781 := by
    have hnat : (2499973897 : ℕ)^1037*100000000000000^781 ≤ 15870398029469^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499973897 10000000000 15870398029469 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4994006721/10000000000 : ℝ)^1037 ≤ (621477381087/1562500000000 : ℝ)^781 := by
    have hnat : (4994006721 : ℕ)^1037*1562500000000^781 ≤ 621477381087^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994006721 10000000000 621477381087 1562500000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355316781/2500000000 : ℝ), (-2499973897/10000000000 : ℝ), (4994006721/10000000000 : ℝ)] ![(44355049565979/100000000000000 : ℝ), (15870398029469/100000000000000 : ℝ), (621477381087/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355316781/2500000000 : ℝ)|^1037 ≤ (44355049565979/100000000000000 : ℝ)^781
        have hw : |(1355316781/2500000000 : ℝ)|=(1355316781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2499973897/10000000000 : ℝ)|^1037 ≤ (15870398029469/100000000000000 : ℝ)^781
        have hw : |(-2499973897/10000000000 : ℝ)|=(2499973897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4994006721/10000000000 : ℝ)|^1037 ≤ (621477381087/1562500000000 : ℝ)^781
        have hw : |(4994006721/10000000000 : ℝ)|=(4994006721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2710634131/5000000000 : ℝ)*x 0 + (2497002807/5000000000 : ℝ)*x 1 + (-2499973819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710634131/5000000000 : ℝ)^1037 ≤ (44355061928649/100000000000000 : ℝ)^781 := by
    have hnat : (2710634131 : ℕ)^1037*100000000000000^781 ≤ 44355061928649^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710634131 5000000000 44355061928649 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497002807/5000000000 : ℝ)^1037 ≤ (39774540682949/100000000000000 : ℝ)^781 := by
    have hnat : (2497002807 : ℕ)^1037*100000000000000^781 ≤ 39774540682949^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497002807 5000000000 39774540682949 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2499973819/10000000000 : ℝ)^1037 ≤ (15870397372001/100000000000000 : ℝ)^781 := by
    have hnat : (2499973819 : ℕ)^1037*100000000000000^781 ≤ 15870397372001^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499973819 10000000000 15870397372001 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710634131/5000000000 : ℝ), (2497002807/5000000000 : ℝ), (-2499973819/10000000000 : ℝ)] ![(44355061928649/100000000000000 : ℝ), (39774540682949/100000000000000 : ℝ), (15870397372001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710634131/5000000000 : ℝ)|^1037 ≤ (44355061928649/100000000000000 : ℝ)^781
        have hw : |(2710634131/5000000000 : ℝ)|=(2710634131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497002807/5000000000 : ℝ)|^1037 ≤ (39774540682949/100000000000000 : ℝ)^781
        have hw : |(2497002807/5000000000 : ℝ)|=(2497002807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2499973819/10000000000 : ℝ)|^1037 ≤ (15870397372001/100000000000000 : ℝ)^781
        have hw : |(-2499973819/10000000000 : ℝ)|=(2499973819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4320724709/10000000000 : ℝ)*x 0 + (183483481/500000000 : ℝ)*x 1 + (5087284967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320724709/10000000000 : ℝ)^1037 ≤ (32816900113787/100000000000000 : ℝ)^781 := by
    have hnat : (4320724709 : ℕ)^1037*100000000000000^781 ≤ 32816900113787^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320724709 10000000000 32816900113787 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183483481/500000000 : ℝ)^1037 ≤ (6604778731853/25000000000000 : ℝ)^781 := by
    have hnat : (183483481 : ℕ)^1037*25000000000000^781 ≤ 6604778731853^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183483481 500000000 6604778731853 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5087284967/10000000000 : ℝ)^1037 ≤ (8152796988421/20000000000000 : ℝ)^781 := by
    have hnat : (5087284967 : ℕ)^1037*20000000000000^781 ≤ 8152796988421^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087284967 10000000000 8152796988421 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320724709/10000000000 : ℝ), (183483481/500000000 : ℝ), (5087284967/10000000000 : ℝ)] ![(32816900113787/100000000000000 : ℝ), (6604778731853/25000000000000 : ℝ), (8152796988421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320724709/10000000000 : ℝ)|^1037 ≤ (32816900113787/100000000000000 : ℝ)^781
        have hw : |(4320724709/10000000000 : ℝ)|=(4320724709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183483481/500000000 : ℝ)|^1037 ≤ (6604778731853/25000000000000 : ℝ)^781
        have hw : |(183483481/500000000 : ℝ)|=(183483481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5087284967/10000000000 : ℝ)|^1037 ≤ (8152796988421/20000000000000 : ℝ)^781
        have hw : |(5087284967/10000000000 : ℝ)|=(5087284967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-264069841/1250000000 : ℝ)*x 0 + (5003957809/10000000000 : ℝ)*x 1 + (5701903151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264069841/1250000000 : ℝ)^1037 ≤ (12690867620371/100000000000000 : ℝ)^781 := by
    have hnat : (264069841 : ℕ)^1037*100000000000000^781 ≤ 12690867620371^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264069841 1250000000 12690867620371 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003957809/10000000000 : ℝ)^1037 ≤ (19939910175207/50000000000000 : ℝ)^781 := by
    have hnat : (5003957809 : ℕ)^1037*50000000000000^781 ≤ 19939910175207^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003957809 10000000000 19939910175207 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5701903151/10000000000 : ℝ)^1037 ≤ (23714656004907/50000000000000 : ℝ)^781 := by
    have hnat : (5701903151 : ℕ)^1037*50000000000000^781 ≤ 23714656004907^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701903151 10000000000 23714656004907 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264069841/1250000000 : ℝ), (5003957809/10000000000 : ℝ), (5701903151/10000000000 : ℝ)] ![(12690867620371/100000000000000 : ℝ), (19939910175207/50000000000000 : ℝ), (23714656004907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264069841/1250000000 : ℝ)|^1037 ≤ (12690867620371/100000000000000 : ℝ)^781
        have hw : |(-264069841/1250000000 : ℝ)|=(264069841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003957809/10000000000 : ℝ)|^1037 ≤ (19939910175207/50000000000000 : ℝ)^781
        have hw : |(5003957809/10000000000 : ℝ)|=(5003957809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5701903151/10000000000 : ℝ)|^1037 ≤ (23714656004907/50000000000000 : ℝ)^781
        have hw : |(5701903151/10000000000 : ℝ)|=(5701903151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1309384153/2500000000 : ℝ)*x 0 + (-358415429/2000000000 : ℝ)*x 1 + (5701902973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309384153/2500000000 : ℝ)^1037 ≤ (42370263965249/100000000000000 : ℝ)^781 := by
    have hnat : (1309384153 : ℕ)^1037*100000000000000^781 ≤ 42370263965249^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309384153 2500000000 42370263965249 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358415429/2000000000 : ℝ)^1037 ≤ (1020042597981/10000000000000 : ℝ)^781 := by
    have hnat : (358415429 : ℕ)^1037*10000000000000^781 ≤ 1020042597981^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358415429 2000000000 1020042597981 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5701902973/10000000000 : ℝ)^1037 ≤ (23714655021927/50000000000000 : ℝ)^781 := by
    have hnat : (5701902973 : ℕ)^1037*50000000000000^781 ≤ 23714655021927^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701902973 10000000000 23714655021927 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309384153/2500000000 : ℝ), (-358415429/2000000000 : ℝ), (5701902973/10000000000 : ℝ)] ![(42370263965249/100000000000000 : ℝ), (1020042597981/10000000000000 : ℝ), (23714655021927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309384153/2500000000 : ℝ)|^1037 ≤ (42370263965249/100000000000000 : ℝ)^781
        have hw : |(1309384153/2500000000 : ℝ)|=(1309384153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358415429/2000000000 : ℝ)|^1037 ≤ (1020042597981/10000000000000 : ℝ)^781
        have hw : |(-358415429/2000000000 : ℝ)|=(358415429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5701902973/10000000000 : ℝ)|^1037 ≤ (23714655021927/50000000000000 : ℝ)^781
        have hw : |(5701902973/10000000000 : ℝ)|=(5701902973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1047507327/2000000000 : ℝ)*x 0 + (2850951553/5000000000 : ℝ)*x 1 + (-1792076917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047507327/2000000000 : ℝ)^1037 ≤ (21185132106151/50000000000000 : ℝ)^781 := by
    have hnat : (1047507327 : ℕ)^1037*50000000000000^781 ≤ 21185132106151^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047507327 2000000000 21185132106151 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850951553/5000000000 : ℝ)^1037 ≤ (47429311512801/100000000000000 : ℝ)^781 := by
    have hnat : (2850951553 : ℕ)^1037*100000000000000^781 ≤ 47429311512801^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850951553 5000000000 47429311512801 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792076917/10000000000 : ℝ)^1037 ≤ (637526516041/6250000000000 : ℝ)^781 := by
    have hnat : (1792076917 : ℕ)^1037*6250000000000^781 ≤ 637526516041^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792076917 10000000000 637526516041 6250000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047507327/2000000000 : ℝ), (2850951553/5000000000 : ℝ), (-1792076917/10000000000 : ℝ)] ![(21185132106151/50000000000000 : ℝ), (47429311512801/100000000000000 : ℝ), (637526516041/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047507327/2000000000 : ℝ)|^1037 ≤ (21185132106151/50000000000000 : ℝ)^781
        have hw : |(1047507327/2000000000 : ℝ)|=(1047507327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850951553/5000000000 : ℝ)|^1037 ≤ (47429311512801/100000000000000 : ℝ)^781
        have hw : |(2850951553/5000000000 : ℝ)|=(2850951553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792076917/10000000000 : ℝ)|^1037 ≤ (637526516041/6250000000000 : ℝ)^781
        have hw : |(-1792076917/10000000000 : ℝ)|=(1792076917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s1_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (172897019/400000000 : ℝ)*x 0 + (633454931/1250000000 : ℝ)*x 1 + (3689709113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172897019/400000000 : ℝ)^1037 ≤ (32834053160119/100000000000000 : ℝ)^781 := by
    have hnat : (172897019 : ℕ)^1037*100000000000000^781 ≤ 32834053160119^781*400000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172897019 400000000 32834053160119 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633454931/1250000000 : ℝ)^1037 ≤ (20277550127277/50000000000000 : ℝ)^781 := by
    have hnat : (633454931 : ℕ)^1037*50000000000000^781 ≤ 20277550127277^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633454931 1250000000 20277550127277 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3689709113/10000000000 : ℝ)^1037 ≤ (26610846569377/100000000000000 : ℝ)^781 := by
    have hnat : (3689709113 : ℕ)^1037*100000000000000^781 ≤ 26610846569377^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689709113 10000000000 26610846569377 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172897019/400000000 : ℝ), (633454931/1250000000 : ℝ), (3689709113/10000000000 : ℝ)] ![(32834053160119/100000000000000 : ℝ), (20277550127277/50000000000000 : ℝ), (26610846569377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172897019/400000000 : ℝ)|^1037 ≤ (32834053160119/100000000000000 : ℝ)^781
        have hw : |(172897019/400000000 : ℝ)|=(172897019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(633454931/1250000000 : ℝ)|^1037 ≤ (20277550127277/50000000000000 : ℝ)^781
        have hw : |(633454931/1250000000 : ℝ)|=(633454931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3689709113/10000000000 : ℝ)|^1037 ≤ (26610846569377/100000000000000 : ℝ)^781
        have hw : |(3689709113/10000000000 : ℝ)|=(3689709113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5593/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2577/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5593/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5593/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5593/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5593/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5593/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5593/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/25000 : ℝ) ^ (8295/2048 : ℝ) ≤ (119390803/4000000000000000000 : ℝ) := by
    have hpowers : (63/25000 : ℝ)^8295 ≤ (119390803/4000000000000000000 : ℝ)^2048 := by
      have hnat : (63 : ℕ)^8295*4000000000000000000^2048 ≤ 119390803^2048*25000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 25000 119390803 4000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/25000 : ℝ)) (X := (119390803/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5593/20000 : ℝ) ^ (8295/2048 : ℝ) ≤ (143406197356793881/25000000000000000000 : ℝ) := by
    have hpowers : (5593/20000 : ℝ)^8295 ≤ (143406197356793881/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5593 : ℕ)^8295*25000000000000000000^2048 ≤ 143406197356793881^2048*20000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5593 20000 143406197356793881 25000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5593/20000 : ℝ)) (X := (143406197356793881/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000000119390803/2000000000000000000 : ℝ) ≤ (5000000000073693/5000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (2000000000119390803/2000000000000000000 : ℝ)^2048 ≤ (5000000000073693/5000000000000000 : ℝ)^8295 := by
      have hnat : (2000000000119390803 : ℕ)^2048*5000000000000000^8295 ≤ 5000000000073693^8295*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000000119390803 2000000000000000000 5000000000073693 5000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000073693/5000000000000000 : ℝ)) (X := (2000000000119390803/2000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100573624792411945599/100000000000000000000 : ℝ) ≤ (400565282468519/400000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (100573624792411945599/100000000000000000000 : ℝ)^2048 ≤ (400565282468519/400000000000000 : ℝ)^8295 := by
      have hnat : (100573624792411945599 : ℕ)^2048*400000000000000^8295 ≤ 400565282468519^8295*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100573624792411945599 100000000000000000000 400565282468519 400000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400565282468519/400000000000000 : ℝ)) (X := (100573624792411945599/100000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12643406197356793881/12500000000000000000 : ℝ) ≤ (2507066030819641/2500000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (12643406197356793881/12500000000000000000 : ℝ)^2048 ≤ (2507066030819641/2500000000000000 : ℝ)^8295 := by
      have hnat : (12643406197356793881 : ℕ)^2048*2500000000000000^8295 ≤ 2507066030819641^8295*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12643406197356793881 12500000000000000000 2507066030819641 2500000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507066030819641/2500000000000000 : ℝ)) (X := (12643406197356793881/12500000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(119390803/4000000000000000000 : ℝ) ≤ ((19794491246075389383/19795000000000000000 : ℝ)+2*(14132061565589/2771300000000000 : ℝ)*(63/25000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (19794491246075389383/19795000000000000000 : ℝ)+2*(14132061565589/2771300000000000 : ℝ)*(63/25000 : ℝ)=(5000000000073693/5000000000000000 : ℝ) by norm_num, show 1+2*(119390803/4000000000000000000 : ℝ)=(2000000000119390803/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(143406197356793881/25000000000000000000 : ℝ)+(119390803/4000000000000000000 : ℝ) ≤ ((19794491246075389383/19795000000000000000 : ℝ)+(14132061565589/2771300000000000 : ℝ)*((5593/20000 : ℝ)+(63/25000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (19794491246075389383/19795000000000000000 : ℝ)+(14132061565589/2771300000000000 : ℝ)*((5593/20000 : ℝ)+(63/25000 : ℝ))=(400565282468519/400000000000000 : ℝ) by norm_num, show 1+(143406197356793881/25000000000000000000 : ℝ)+(119390803/4000000000000000000 : ℝ)=(100573624792411945599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(143406197356793881/25000000000000000000 : ℝ) ≤ ((19794491246075389383/19795000000000000000 : ℝ)+2*(14132061565589/2771300000000000 : ℝ)*(5593/20000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (19794491246075389383/19795000000000000000 : ℝ)+2*(14132061565589/2771300000000000 : ℝ)*(5593/20000 : ℝ)=(2507066030819641/2500000000000000 : ℝ) by norm_num, show 1+2*(143406197356793881/25000000000000000000 : ℝ)=(12643406197356793881/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19794491246075389383/19795000000000000000 : ℝ)*(X 1 0+X 2 0)+(14132061565589/2771300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (63/25000 : ℝ)) (hi := (5593/20000 : ℝ)) (c := (19794491246075389383/19795000000000000000 : ℝ)) (alpha := (14132061565589/2771300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19794491246075389383/19795000000000000000 : ℝ)*(X 0 1+X 2 1)+(14132061565589/2771300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (63/25000 : ℝ)) (hi := (5593/20000 : ℝ)) (c := (19794491246075389383/19795000000000000000 : ℝ)) (alpha := (14132061565589/2771300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19794491246075389383/19795000000000000000 : ℝ)*(X 0 2+X 1 2)+(14132061565589/2771300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (63/25000 : ℝ)) (hi := (5593/20000 : ℝ)) (c := (19794491246075389383/19795000000000000000 : ℝ)) (alpha := (14132061565589/2771300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-131981039/625000000 : ℝ)*X 0 0+(2856026951/5000000000 : ℝ)*X 0 1+(62425083/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1355316781/2500000000 : ℝ)*X 1 0+(-2499973897/10000000000 : ℝ)*X 1 1+(4994006721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710634131/5000000000 : ℝ)*X 2 0+(2497002807/5000000000 : ℝ)*X 2 1+(-2499973819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320724709/10000000000 : ℝ)*X 0 0+(183483481/500000000 : ℝ)*X 0 1+(5087284967/10000000000 : ℝ)*X 0 2+(4320724709/10000000000 : ℝ)*X 1 0+(183483481/500000000 : ℝ)*X 1 1+(5087284967/10000000000 : ℝ)*X 1 2+(4320724709/10000000000 : ℝ)*X 2 0+(183483481/500000000 : ℝ)*X 2 1+(5087284967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264069841/1250000000 : ℝ)*X 0 0+(5003957809/10000000000 : ℝ)*X 0 1+(5701903151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309384153/2500000000 : ℝ)*X 1 0+(-358415429/2000000000 : ℝ)*X 1 1+(5701902973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047507327/2000000000 : ℝ)*X 2 0+(2850951553/5000000000 : ℝ)*X 2 1+(-1792076917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172897019/400000000 : ℝ)*X 0 0+(633454931/1250000000 : ℝ)*X 0 1+(3689709113/10000000000 : ℝ)*X 0 2+(172897019/400000000 : ℝ)*X 1 0+(633454931/1250000000 : ℝ)*X 1 1+(3689709113/10000000000 : ℝ)*X 1 2+(172897019/400000000 : ℝ)*X 2 0+(633454931/1250000000 : ℝ)*X 2 1+(3689709113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5692715383636918671697587849/3464125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76197743/50000000000000 : ℝ)*(base1) + (159017971/100000000000000 : ℝ)*(base19) + (478495653/100000000000000 : ℝ)*(base23) + (437783/3125000000000 : ℝ)*(base37) + (11712411/50000000000000 : ℝ)*(upper3) + (524519119708319/50000000000000 : ℝ)*(major0) + (524519119708319/50000000000000 : ℝ)*(major1) + (524519119708319/50000000000000 : ℝ)*(major2) + (348166566316337/25000000000000 : ℝ)*(sp0) + (1392665831710317/100000000000000 : ℝ)*(sp1) + (696333156484189/50000000000000 : ℝ)*(sp2) + (88176183273361/12500000000000 : ℝ)*(sp3) + (678594169/100000000000000 : ℝ)*(sp4) + (800735743/100000000000000 : ℝ)*(sp5) + (705409632591431/100000000000000 : ℝ)*(f.failure) + (1392666791464031/100000000000000 : ℝ)*(f.sum) + (110106438795131/69282500000000000000000000000 : ℝ)*base65 + (20359143782109940239/6928250000000000000000000000000000 : ℝ)*base67 + (53275233495746440239/6928250000000000000000000000000000 : ℝ)*base69 + (12699891083108190239/6928250000000000000000000000000000 : ℝ)*base71 + (117818961983921/69282500000000000000000000000 : ℝ)*base73 + (40271827922436190239/6928250000000000000000000000000000 : ℝ)*base75 + (27126045571469190239/6928250000000000000000000000000000 : ℝ)*base77 + (9840186363691190239/6928250000000000000000000000000000 : ℝ)*base79 + (183459890867093/34641250000000000000000000000 : ℝ)*base81 + (12286201/5000000000000000000000 : ℝ)*base89 + (12286201/5000000000000000000000 : ℝ)*base91 + (12286201/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5647158178707048236557697529/1385650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50796917/100000000000000 : ℝ)*(base1) + (923903843/100000000000000 : ℝ)*(base19) + (189223173/20000000000000 : ℝ)*(base23) + (44363571/50000000000000 : ℝ)*(upper3) + (18023263/20000000000000 : ℝ)*(upper5) + (215850327541601/20000000000000 : ℝ)*(major0) + (215850327541601/20000000000000 : ℝ)*(major1) + (215850327541601/20000000000000 : ℝ)*(major2) + (224175111/6250000000000 : ℝ)*(sp1) + (2020303657/50000000000000 : ℝ)*(sp2) + (1432777022696057/100000000000000 : ℝ)*(sp4) + (1432772461193521/100000000000000 : ℝ)*(sp5) + (35819299629399/2500000000000 : ℝ)*(sp6) + (90715764608919/12500000000000 : ℝ)*(sp7) + (181431541917067/25000000000000 : ℝ)*(f.failure) + (71638848594957/5000000000000 : ℝ)*(f.sum) + (16238800569963/27713000000000000000000000000 : ℝ)*base66 + (21342589554738694719/2771300000000000000000000000000000 : ℝ)*base68 + (15126989254364894719/2771300000000000000000000000000000 : ℝ)*base70 + (19621175683535794719/2771300000000000000000000000000000 : ℝ)*base72 + (4529435748169/13856500000000000000000000000 : ℝ)*base74 + (28521787409773494719/2771300000000000000000000000000000 : ℝ)*base76 + (3066149445105394719/2771300000000000000000000000000000 : ℝ)*base78 + (14988922725324594719/2771300000000000000000000000000000 : ℝ)*base80 + (20124906992219/27713000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2296043/1250000000000000000000 : ℝ)*base90 + (2296043/1250000000000000000000 : ℝ)*base92 + (2296043/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1103_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5593/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2577/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1103_s2_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-108352511/500000000 : ℝ)*x 0 + (2759191911/5000000000 : ℝ)*x 1 + (5152519133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108352511/500000000 : ℝ)^1037 ≤ (1312734383309/10000000000000 : ℝ)^781 := by
    have hnat : (108352511 : ℕ)^1037*10000000000000^781 ≤ 1312734383309^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108352511 500000000 1312734383309 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2759191911/5000000000 : ℝ)^1037 ≤ (22706581265207/50000000000000 : ℝ)^781 := by
    have hnat : (2759191911 : ℕ)^1037*50000000000000^781 ≤ 22706581265207^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759191911 5000000000 22706581265207 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152519133/10000000000 : ℝ)^1037 ≤ (20729746809173/50000000000000 : ℝ)^781 := by
    have hnat : (5152519133 : ℕ)^1037*50000000000000^781 ≤ 20729746809173^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152519133 10000000000 20729746809173 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108352511/500000000 : ℝ), (2759191911/5000000000 : ℝ), (5152519133/10000000000 : ℝ)] ![(1312734383309/10000000000000 : ℝ), (22706581265207/50000000000000 : ℝ), (20729746809173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108352511/500000000 : ℝ)|^1037 ≤ (1312734383309/10000000000000 : ℝ)^781
        have hw : |(-108352511/500000000 : ℝ)|=(108352511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2759191911/5000000000 : ℝ)|^1037 ≤ (22706581265207/50000000000000 : ℝ)^781
        have hw : |(2759191911/5000000000 : ℝ)|=(2759191911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152519133/10000000000 : ℝ)|^1037 ≤ (20729746809173/50000000000000 : ℝ)^781
        have hw : |(5152519133/10000000000 : ℝ)|=(5152519133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2687778457/5000000000 : ℝ)*x 0 + (-2357559493/10000000000 : ℝ)*x 1 + (161016259/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687778457/5000000000 : ℝ)^1037 ≤ (43859163960033/100000000000000 : ℝ)^781 := by
    have hnat : (2687778457 : ℕ)^1037*100000000000000^781 ≤ 43859163960033^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687778457 5000000000 43859163960033 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2357559493/10000000000 : ℝ)^1037 ≤ (3670332516463/25000000000000 : ℝ)^781 := by
    have hnat : (2357559493 : ℕ)^1037*25000000000000^781 ≤ 3670332516463^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357559493 10000000000 3670332516463 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161016259/312500000 : ℝ)^1037 ≤ (10364876489579/25000000000000 : ℝ)^781 := by
    have hnat : (161016259 : ℕ)^1037*25000000000000^781 ≤ 10364876489579^781*312500000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161016259 312500000 10364876489579 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687778457/5000000000 : ℝ), (-2357559493/10000000000 : ℝ), (161016259/312500000 : ℝ)] ![(43859163960033/100000000000000 : ℝ), (3670332516463/25000000000000 : ℝ), (10364876489579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687778457/5000000000 : ℝ)|^1037 ≤ (43859163960033/100000000000000 : ℝ)^781
        have hw : |(2687778457/5000000000 : ℝ)|=(2687778457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2357559493/10000000000 : ℝ)|^1037 ≤ (3670332516463/25000000000000 : ℝ)^781
        have hw : |(-2357559493/10000000000 : ℝ)|=(2357559493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161016259/312500000 : ℝ)|^1037 ≤ (10364876489579/25000000000000 : ℝ)^781
        have hw : |(161016259/312500000 : ℝ)|=(161016259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5375556869/10000000000 : ℝ)*x 0 + (5152520339/10000000000 : ℝ)*x 1 + (-1178779743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375556869/10000000000 : ℝ)^1037 ≤ (4385916347253/10000000000000 : ℝ)^781 := by
    have hnat : (5375556869 : ℕ)^1037*10000000000000^781 ≤ 4385916347253^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375556869 10000000000 4385916347253 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152520339/10000000000 : ℝ)^1037 ≤ (20729753251599/50000000000000 : ℝ)^781 := by
    have hnat : (5152520339 : ℕ)^1037*50000000000000^781 ≤ 20729753251599^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152520339 10000000000 20729753251599 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178779743/5000000000 : ℝ)^1037 ≤ (3670332501993/25000000000000 : ℝ)^781 := by
    have hnat : (1178779743 : ℕ)^1037*25000000000000^781 ≤ 3670332501993^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178779743 5000000000 3670332501993 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375556869/10000000000 : ℝ), (5152520339/10000000000 : ℝ), (-1178779743/5000000000 : ℝ)] ![(4385916347253/10000000000000 : ℝ), (20729753251599/50000000000000 : ℝ), (3670332501993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375556869/10000000000 : ℝ)|^1037 ≤ (4385916347253/10000000000000 : ℝ)^781
        have hw : |(5375556869/10000000000 : ℝ)|=(5375556869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152520339/10000000000 : ℝ)|^1037 ≤ (20729753251599/50000000000000 : ℝ)^781
        have hw : |(5152520339/10000000000 : ℝ)|=(5152520339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1178779743/5000000000 : ℝ)|^1037 ≤ (3670332501993/25000000000000 : ℝ)^781
        have hw : |(-1178779743/5000000000 : ℝ)|=(1178779743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1089649229/2500000000 : ℝ)*x 0 + (4012402671/10000000000 : ℝ)*x 1 + (4734714849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089649229/2500000000 : ℝ)^1037 ≤ (33199382568197/100000000000000 : ℝ)^781 := by
    have hnat : (1089649229 : ℕ)^1037*100000000000000^781 ≤ 33199382568197^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089649229 2500000000 33199382568197 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012402671/10000000000 : ℝ)^1037 ≤ (14872244133481/50000000000000 : ℝ)^781 := by
    have hnat : (4012402671 : ℕ)^1037*50000000000000^781 ≤ 14872244133481^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012402671 10000000000 14872244133481 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4734714849/10000000000 : ℝ)^1037 ≤ (18528064577307/50000000000000 : ℝ)^781 := by
    have hnat : (4734714849 : ℕ)^1037*50000000000000^781 ≤ 18528064577307^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4734714849 10000000000 18528064577307 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089649229/2500000000 : ℝ), (4012402671/10000000000 : ℝ), (4734714849/10000000000 : ℝ)] ![(33199382568197/100000000000000 : ℝ), (14872244133481/50000000000000 : ℝ), (18528064577307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089649229/2500000000 : ℝ)|^1037 ≤ (33199382568197/100000000000000 : ℝ)^781
        have hw : |(1089649229/2500000000 : ℝ)|=(1089649229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012402671/10000000000 : ℝ)|^1037 ≤ (14872244133481/50000000000000 : ℝ)^781
        have hw : |(4012402671/10000000000 : ℝ)|=(4012402671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4734714849/10000000000 : ℝ)|^1037 ≤ (18528064577307/50000000000000 : ℝ)^781
        have hw : |(4734714849/10000000000 : ℝ)|=(4734714849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167163933/10000000000 : ℝ)*x 0 + (2577556049/5000000000 : ℝ)*x 1 + (2757882197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167163933/10000000000 : ℝ)^1037 ≤ (262565169431/2000000000000 : ℝ)^781 := by
    have hnat : (2167163933 : ℕ)^1037*2000000000000^781 ≤ 262565169431^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167163933 10000000000 262565169431 2000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577556049/5000000000 : ℝ)^1037 ≤ (10371799756927/25000000000000 : ℝ)^781 := by
    have hnat : (2577556049 : ℕ)^1037*25000000000000^781 ≤ 10371799756927^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577556049 5000000000 10371799756927 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757882197/5000000000 : ℝ)^1037 ≤ (22692271245087/50000000000000 : ℝ)^781 := by
    have hnat : (2757882197 : ℕ)^1037*50000000000000^781 ≤ 22692271245087^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757882197 5000000000 22692271245087 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167163933/10000000000 : ℝ), (2577556049/5000000000 : ℝ), (2757882197/5000000000 : ℝ)] ![(262565169431/2000000000000 : ℝ), (10371799756927/25000000000000 : ℝ), (22692271245087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167163933/10000000000 : ℝ)|^1037 ≤ (262565169431/2000000000000 : ℝ)^781
        have hw : |(-2167163933/10000000000 : ℝ)|=(2167163933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577556049/5000000000 : ℝ)|^1037 ≤ (10371799756927/25000000000000 : ℝ)^781
        have hw : |(2577556049/5000000000 : ℝ)|=(2577556049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757882197/5000000000 : ℝ)|^1037 ≤ (22692271245087/50000000000000 : ℝ)^781
        have hw : |(2757882197/5000000000 : ℝ)|=(2757882197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5282971667/10000000000 : ℝ)*x 0 + (-1994314827/10000000000 : ℝ)*x 1 + (5515764481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282971667/10000000000 : ℝ)^1037 ≤ (669671775521/1562500000000 : ℝ)^781 := by
    have hnat : (5282971667 : ℕ)^1037*1562500000000^781 ≤ 669671775521^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282971667 10000000000 669671775521 1562500000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1994314827/10000000000 : ℝ)^1037 ≤ (11756462913253/100000000000000 : ℝ)^781 := by
    have hnat : (1994314827 : ℕ)^1037*100000000000000^781 ≤ 11756462913253^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994314827 10000000000 11756462913253 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515764481/10000000000 : ℝ)^1037 ≤ (11346135860167/25000000000000 : ℝ)^781 := by
    have hnat : (5515764481 : ℕ)^1037*25000000000000^781 ≤ 11346135860167^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515764481 10000000000 11346135860167 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282971667/10000000000 : ℝ), (-1994314827/10000000000 : ℝ), (5515764481/10000000000 : ℝ)] ![(669671775521/1562500000000 : ℝ), (11756462913253/100000000000000 : ℝ), (11346135860167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282971667/10000000000 : ℝ)|^1037 ≤ (669671775521/1562500000000 : ℝ)^781
        have hw : |(5282971667/10000000000 : ℝ)|=(5282971667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1994314827/10000000000 : ℝ)|^1037 ≤ (11756462913253/100000000000000 : ℝ)^781
        have hw : |(-1994314827/10000000000 : ℝ)|=(1994314827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515764481/10000000000 : ℝ)|^1037 ≤ (11346135860167/25000000000000 : ℝ)^781
        have hw : |(5515764481/10000000000 : ℝ)|=(5515764481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (264148591/500000000 : ℝ)*x 0 + (86183819/156250000 : ℝ)*x 1 + (-1994314707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264148591/500000000 : ℝ)^1037 ≤ (42858995281441/100000000000000 : ℝ)^781 := by
    have hnat : (264148591 : ℕ)^1037*100000000000000^781 ≤ 42858995281441^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264148591 500000000 42858995281441 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86183819/156250000 : ℝ)^1037 ≤ (45384542730529/100000000000000 : ℝ)^781 := by
    have hnat : (86183819 : ℕ)^1037*100000000000000^781 ≤ 45384542730529^781*156250000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86183819 156250000 45384542730529 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994314707/10000000000 : ℝ)^1037 ≤ (587823098699/5000000000000 : ℝ)^781 := by
    have hnat : (1994314707 : ℕ)^1037*5000000000000^781 ≤ 587823098699^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994314707 10000000000 587823098699 5000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264148591/500000000 : ℝ), (86183819/156250000 : ℝ), (-1994314707/10000000000 : ℝ)] ![(42858995281441/100000000000000 : ℝ), (45384542730529/100000000000000 : ℝ), (587823098699/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264148591/500000000 : ℝ)|^1037 ≤ (42858995281441/100000000000000 : ℝ)^781
        have hw : |(264148591/500000000 : ℝ)|=(264148591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86183819/156250000 : ℝ)|^1037 ≤ (45384542730529/100000000000000 : ℝ)^781
        have hw : |(86183819/156250000 : ℝ)|=(86183819/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994314707/10000000000 : ℝ)|^1037 ≤ (587823098699/5000000000000 : ℝ)^781
        have hw : |(-1994314707/10000000000 : ℝ)|=(1994314707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_s2_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1089705683/2500000000 : ℝ)*x 0 + (591199571/1250000000 : ℝ)*x 1 + (2008786129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089705683/2500000000 : ℝ)^1037 ≤ (33201666427891/100000000000000 : ℝ)^781 := by
    have hnat : (1089705683 : ℕ)^1037*100000000000000^781 ≤ 33201666427891^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089705683 2500000000 33201666427891 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591199571/1250000000 : ℝ)^1037 ≤ (37002950040091/100000000000000 : ℝ)^781 := by
    have hnat : (591199571 : ℕ)^1037*100000000000000^781 ≤ 37002950040091^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591199571 1250000000 37002950040091 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008786129/5000000000 : ℝ)^1037 ≤ (3724422939313/12500000000000 : ℝ)^781 := by
    have hnat : (2008786129 : ℕ)^1037*12500000000000^781 ≤ 3724422939313^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008786129 5000000000 3724422939313 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089705683/2500000000 : ℝ), (591199571/1250000000 : ℝ), (2008786129/5000000000 : ℝ)] ![(33201666427891/100000000000000 : ℝ), (37002950040091/100000000000000 : ℝ), (3724422939313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089705683/2500000000 : ℝ)|^1037 ≤ (33201666427891/100000000000000 : ℝ)^781
        have hw : |(1089705683/2500000000 : ℝ)|=(1089705683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591199571/1250000000 : ℝ)|^1037 ≤ (37002950040091/100000000000000 : ℝ)^781
        have hw : |(591199571/1250000000 : ℝ)|=(591199571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008786129/5000000000 : ℝ)|^1037 ≤ (3724422939313/12500000000000 : ℝ)^781
        have hw : |(2008786129/5000000000 : ℝ)|=(2008786129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2577/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (889/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8311/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2577/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2577/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2577/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2577/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2577/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2577/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5429/100000 : ℝ) ^ (8295/2048 : ℝ) ≤ (750316800883087/100000000000000000000 : ℝ) := by
    have hpowers : (5429/100000 : ℝ)^8295 ≤ (750316800883087/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5429 : ℕ)^8295*100000000000000000000^2048 ≤ 750316800883087^2048*100000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5429 100000 750316800883087 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5429/100000 : ℝ)) (X := (750316800883087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2577/12500 : ℝ) ^ (8295/2048 : ℝ) ≤ (83425137304397677/50000000000000000000 : ℝ) := by
    have hpowers : (2577/12500 : ℝ)^8295 ≤ (83425137304397677/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2577 : ℕ)^8295*50000000000000000000^2048 ≤ 83425137304397677^2048*12500^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2577 12500 83425137304397677 50000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2577/12500 : ℝ)) (X := (83425137304397677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000750316800883087/50000000000000000000 : ℝ) ≤ (10000037049792049/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50000750316800883087/50000000000000000000 : ℝ)^2048 ≤ (10000037049792049/10000000000000000 : ℝ)^8295 := by
      have hnat : (50000750316800883087 : ℕ)^2048*10000000000000000^8295 ≤ 10000037049792049^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000750316800883087 50000000000000000000 10000037049792049 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037049792049/10000000000000000 : ℝ)) (X := (50000750316800883087/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100167600591409678441/100000000000000000000 : ℝ) ≤ (2501033844482601/2500000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (100167600591409678441/100000000000000000000 : ℝ)^2048 ≤ (2501033844482601/2500000000000000 : ℝ)^8295 := by
      have hnat : (100167600591409678441 : ℕ)^2048*2500000000000000^8295 ≤ 2501033844482601^8295*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100167600591409678441 100000000000000000000 2501033844482601 2500000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501033844482601/2500000000000000 : ℝ)) (X := (100167600591409678441/100000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25083425137304397677/25000000000000000000 : ℝ) ≤ (10008233706068759/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (25083425137304397677/25000000000000000000 : ℝ)^2048 ≤ (10008233706068759/10000000000000000 : ℝ)^8295 := by
      have hnat : (25083425137304397677 : ℕ)^2048*10000000000000000^8295 ≤ 10008233706068759^8295*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25083425137304397677 25000000000000000000 10008233706068759 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008233706068759/10000000000000000 : ℝ)) (X := (25083425137304397677/25000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(750316800883087/100000000000000000000 : ℝ) ≤ ((151826063028265589573/151870000000000000000 : ℝ)+2*(819665627671/303740000000000 : ℝ)*(5429/100000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (151826063028265589573/151870000000000000000 : ℝ)+2*(819665627671/303740000000000 : ℝ)*(5429/100000 : ℝ)=(10000037049792049/10000000000000000 : ℝ) by norm_num, show 1+2*(750316800883087/100000000000000000000 : ℝ)=(50000750316800883087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83425137304397677/50000000000000000000 : ℝ)+(750316800883087/100000000000000000000 : ℝ) ≤ ((151826063028265589573/151870000000000000000 : ℝ)+(819665627671/303740000000000 : ℝ)*((2577/12500 : ℝ)+(5429/100000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (151826063028265589573/151870000000000000000 : ℝ)+(819665627671/303740000000000 : ℝ)*((2577/12500 : ℝ)+(5429/100000 : ℝ))=(2501033844482601/2500000000000000 : ℝ) by norm_num, show 1+(83425137304397677/50000000000000000000 : ℝ)+(750316800883087/100000000000000000000 : ℝ)=(100167600591409678441/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83425137304397677/50000000000000000000 : ℝ) ≤ ((151826063028265589573/151870000000000000000 : ℝ)+2*(819665627671/303740000000000 : ℝ)*(2577/12500 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (151826063028265589573/151870000000000000000 : ℝ)+2*(819665627671/303740000000000 : ℝ)*(2577/12500 : ℝ)=(10008233706068759/10000000000000000 : ℝ) by norm_num, show 1+2*(83425137304397677/50000000000000000000 : ℝ)=(25083425137304397677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (151826063028265589573/151870000000000000000 : ℝ)*(X 1 0+X 2 0)+(819665627671/303740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5429/100000 : ℝ)) (hi := (2577/12500 : ℝ)) (c := (151826063028265589573/151870000000000000000 : ℝ)) (alpha := (819665627671/303740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (151826063028265589573/151870000000000000000 : ℝ)*(X 0 1+X 2 1)+(819665627671/303740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5429/100000 : ℝ)) (hi := (2577/12500 : ℝ)) (c := (151826063028265589573/151870000000000000000 : ℝ)) (alpha := (819665627671/303740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (151826063028265589573/151870000000000000000 : ℝ)*(X 0 2+X 1 2)+(819665627671/303740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5429/100000 : ℝ)) (hi := (2577/12500 : ℝ)) (c := (151826063028265589573/151870000000000000000 : ℝ)) (alpha := (819665627671/303740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108352511/500000000 : ℝ)*X 0 0+(2759191911/5000000000 : ℝ)*X 0 1+(5152519133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687778457/5000000000 : ℝ)*X 1 0+(-2357559493/10000000000 : ℝ)*X 1 1+(161016259/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375556869/10000000000 : ℝ)*X 2 0+(5152520339/10000000000 : ℝ)*X 2 1+(-1178779743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089649229/2500000000 : ℝ)*X 0 0+(4012402671/10000000000 : ℝ)*X 0 1+(4734714849/10000000000 : ℝ)*X 0 2+(1089649229/2500000000 : ℝ)*X 1 0+(4012402671/10000000000 : ℝ)*X 1 1+(4734714849/10000000000 : ℝ)*X 1 2+(1089649229/2500000000 : ℝ)*X 2 0+(4012402671/10000000000 : ℝ)*X 2 1+(4734714849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167163933/10000000000 : ℝ)*X 0 0+(2577556049/5000000000 : ℝ)*X 0 1+(2757882197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282971667/10000000000 : ℝ)*X 1 0+(-1994314827/10000000000 : ℝ)*X 1 1+(5515764481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264148591/500000000 : ℝ)*X 2 0+(86183819/156250000 : ℝ)*X 2 1+(-1994314707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089705683/2500000000 : ℝ)*X 0 0+(591199571/1250000000 : ℝ)*X 0 1+(2008786129/5000000000 : ℝ)*X 0 2+(1089705683/2500000000 : ℝ)*X 1 0+(591199571/1250000000 : ℝ)*X 1 1+(2008786129/5000000000 : ℝ)*X 1 2+(1089705683/2500000000 : ℝ)*X 2 0+(591199571/1250000000 : ℝ)*X 2 1+(2008786129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2079338119270858878244533993/237296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (219226599/20000000000000 : ℝ)*(base19) + (169165247/20000000000000 : ℝ)*(base23) + (28151207/12500000000000 : ℝ)*(upper3) + (122254037/100000000000000 : ℝ)*(upper4) + (49746023/100000000000000 : ℝ)*(upper5) + (64339747376903/3125000000000 : ℝ)*(major0) + (64339747376903/3125000000000 : ℝ)*(major1) + (64339747376903/3125000000000 : ℝ)*(major2) + (1366634830699089/50000000000000 : ℝ)*(sp0) + (2733285684090349/100000000000000 : ℝ)*(sp1) + (2733285934397109/100000000000000 : ℝ)*(sp2) + (1384448978386103/100000000000000 : ℝ)*(sp3) + (3423765033/20000000000000 : ℝ)*(sp4) + (4863391/62500000000 : ℝ)*(sp7) + (1384456759811703/100000000000000 : ℝ)*(f.failure) + (170830423763959/6250000000000 : ℝ)*(f.sum) + (234035024501/121496000000000000000000000 : ℝ)*base66 + (3290922826006426169/474593750000000000000000000000000 : ℝ)*base67 + (2664070605835051169/474593750000000000000000000000000 : ℝ)*base69 + (372467345936269919/474593750000000000000000000000000 : ℝ)*base71 + (3130310312857/1898375000000000000000000000 : ℝ)*base74 + (5002035511972323831/474593750000000000000000000000000 : ℝ)*base76 + (1658109193484863669/474593750000000000000000000000000 : ℝ)*base77 + (890949307148417581/474593750000000000000000000000000 : ℝ)*base80 + (7035151281367/3037400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (21920713/5000000000000000000000 : ℝ)*base89 + (21920713/5000000000000000000000 : ℝ)*base91 + (21920713/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37278698699552426135504685651/3796750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1956362021/100000000000000 : ℝ)*(base19) + (1109816929/50000000000000 : ℝ)*(base23) + (31749231/12500000000000 : ℝ)*(upper3) + (33785091/50000000000000 : ℝ)*(lower4) + (97935813/50000000000000 : ℝ)*(upper5) + (1044299921823743/50000000000000 : ℝ)*(major0) + (1044299921823743/50000000000000 : ℝ)*(major1) + (1044299921823743/50000000000000 : ℝ)*(major2) + (8911469443/50000000000000 : ℝ)*(sp1) + (10482611759/50000000000000 : ℝ)*(sp2) + (1386376256215261/50000000000000 : ℝ)*(sp4) + (173295795820601/6250000000000 : ℝ)*(sp5) + (1386364663786573/50000000000000 : ℝ)*(sp6) + (1404446847578401/100000000000000 : ℝ)*(sp7) + (1404446847578401/100000000000000 : ℝ)*(f.failure) + (1386376256215261/50000000000000 : ℝ)*(f.sum) + (3527367281121/3796750000000000000000000000 : ℝ)*base65 + (57139015031832868261/7593500000000000000000000000000000 : ℝ)*base68 + (17955417540719868261/7593500000000000000000000000000000 : ℝ)*base70 + (31655048944386868261/7593500000000000000000000000000000 : ℝ)*base72 + (2536040091/6074800000000000000000000 : ℝ)*base74 + (49503788734145868261/7593500000000000000000000000000000 : ℝ)*base76 + (43870280977277868261/7593500000000000000000000000000000 : ℝ)*base78 + (20488608988849868261/7593500000000000000000000000000000 : ℝ)*base80 + (374495670217/303740000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9863071/5000000000000000000000 : ℝ)*base89 + (9863071/5000000000000000000000 : ℝ)*base91 + (9863071/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1103_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2577/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8311/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1103_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1103_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8311/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1103_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1103_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1103_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8311/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
