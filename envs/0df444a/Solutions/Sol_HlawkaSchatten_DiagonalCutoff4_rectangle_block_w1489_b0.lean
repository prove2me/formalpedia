-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:00.174856+00:00
-- url     : https://prove2.me/submissions/bcc72943-ab54-4dba-b8c4-b3f9ba15c1ef

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
theorem support_rectangle_w1489_s0_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1710502149/10000000000 : ℝ)*x 0 + (5930758399/10000000000 : ℝ)*x 1 + (1211339261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1710502149/10000000000 : ℝ)^4475 ≤ (2025824304457/20000000000000 : ℝ)^3451 := by
    have hnat : (1710502149 : ℕ)^4475*20000000000000^3451 ≤ 2025824304457^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710502149 10000000000 2025824304457 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5930758399/10000000000 : ℝ)^4475 ≤ (25395468987709/50000000000000 : ℝ)^3451 := by
    have hnat : (5930758399 : ℕ)^4475*50000000000000^3451 ≤ 25395468987709^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930758399 10000000000 25395468987709 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211339261/2500000000 : ℝ)^4475 ≤ (9769985120953/25000000000000 : ℝ)^3451 := by
    have hnat : (1211339261 : ℕ)^4475*25000000000000^3451 ≤ 9769985120953^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211339261 2500000000 9769985120953 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1710502149/10000000000 : ℝ), (5930758399/10000000000 : ℝ), (1211339261/2500000000 : ℝ)] ![(2025824304457/20000000000000 : ℝ), (25395468987709/50000000000000 : ℝ), (9769985120953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1710502149/10000000000 : ℝ)|^4475 ≤ (2025824304457/20000000000000 : ℝ)^3451
        have hw : |(-1710502149/10000000000 : ℝ)|=(1710502149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5930758399/10000000000 : ℝ)|^4475 ≤ (25395468987709/50000000000000 : ℝ)^3451
        have hw : |(5930758399/10000000000 : ℝ)|=(5930758399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1211339261/2500000000 : ℝ)|^4475 ≤ (9769985120953/25000000000000 : ℝ)^3451
        have hw : |(1211339261/2500000000 : ℝ)|=(1211339261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5483002023/10000000000 : ℝ)*x 0 + (-464143811/2000000000 : ℝ)*x 1 + (96907141/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483002023/10000000000 : ℝ)^4475 ≤ (11468813703001/25000000000000 : ℝ)^3451 := by
    have hnat : (5483002023 : ℕ)^4475*25000000000000^3451 ≤ 11468813703001^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483002023 10000000000 11468813703001 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464143811/2000000000 : ℝ)^4475 ≤ (3008960926443/20000000000000 : ℝ)^3451 := by
    have hnat : (464143811 : ℕ)^4475*20000000000000^3451 ≤ 3008960926443^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464143811 2000000000 3008960926443 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96907141/200000000 : ℝ)^4475 ≤ (9769985136641/25000000000000 : ℝ)^3451 := by
    have hnat : (96907141 : ℕ)^4475*25000000000000^3451 ≤ 9769985136641^3451*200000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96907141 200000000 9769985136641 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483002023/10000000000 : ℝ), (-464143811/2000000000 : ℝ), (96907141/200000000 : ℝ)] ![(11468813703001/25000000000000 : ℝ), (3008960926443/20000000000000 : ℝ), (9769985136641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483002023/10000000000 : ℝ)|^4475 ≤ (11468813703001/25000000000000 : ℝ)^3451
        have hw : |(5483002023/10000000000 : ℝ)|=(5483002023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464143811/2000000000 : ℝ)|^4475 ≤ (3008960926443/20000000000000 : ℝ)^3451
        have hw : |(-464143811/2000000000 : ℝ)|=(464143811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96907141/200000000 : ℝ)|^4475 ≤ (9769985136641/25000000000000 : ℝ)^3451
        have hw : |(96907141/200000000 : ℝ)|=(96907141/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2741501007/5000000000 : ℝ)*x 0 + (4845357073/10000000000 : ℝ)*x 1 + (-2320719037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741501007/5000000000 : ℝ)^4475 ≤ (45875254714359/100000000000000 : ℝ)^3451 := by
    have hnat : (2741501007 : ℕ)^4475*100000000000000^3451 ≤ 45875254714359^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741501007 5000000000 45875254714359 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4845357073/10000000000 : ℝ)^4475 ≤ (39079940787113/100000000000000 : ℝ)^3451 := by
    have hnat : (4845357073 : ℕ)^4475*100000000000000^3451 ≤ 39079940787113^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845357073 10000000000 39079940787113 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320719037/10000000000 : ℝ)^4475 ≤ (15044804480899/100000000000000 : ℝ)^3451 := by
    have hnat : (2320719037 : ℕ)^4475*100000000000000^3451 ≤ 15044804480899^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320719037 10000000000 15044804480899 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741501007/5000000000 : ℝ), (4845357073/10000000000 : ℝ), (-2320719037/10000000000 : ℝ)] ![(45875254714359/100000000000000 : ℝ), (39079940787113/100000000000000 : ℝ), (15044804480899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741501007/5000000000 : ℝ)|^4475 ≤ (45875254714359/100000000000000 : ℝ)^3451
        have hw : |(2741501007/5000000000 : ℝ)|=(2741501007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4845357073/10000000000 : ℝ)|^4475 ≤ (39079940787113/100000000000000 : ℝ)^3451
        have hw : |(4845357073/10000000000 : ℝ)|=(4845357073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2320719037/10000000000 : ℝ)|^4475 ≤ (15044804480899/100000000000000 : ℝ)^3451
        have hw : |(-2320719037/10000000000 : ℝ)|=(2320719037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2075702149/5000000000 : ℝ)*x 0 + (3091323297/10000000000 : ℝ)*x 1 + (5512727049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075702149/5000000000 : ℝ)^4475 ≤ (7995465169567/25000000000000 : ℝ)^3451 := by
    have hnat : (2075702149 : ℕ)^4475*25000000000000^3451 ≤ 7995465169567^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075702149 5000000000 7995465169567 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091323297/10000000000 : ℝ)^4475 ≤ (21820124927401/100000000000000 : ℝ)^3451 := by
    have hnat : (3091323297 : ℕ)^4475*100000000000000^3451 ≤ 21820124927401^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091323297 10000000000 21820124927401 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5512727049/10000000000 : ℝ)^4475 ≤ (46198014387569/100000000000000 : ℝ)^3451 := by
    have hnat : (5512727049 : ℕ)^4475*100000000000000^3451 ≤ 46198014387569^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512727049 10000000000 46198014387569 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2075702149/5000000000 : ℝ), (3091323297/10000000000 : ℝ), (5512727049/10000000000 : ℝ)] ![(7995465169567/25000000000000 : ℝ), (21820124927401/100000000000000 : ℝ), (46198014387569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2075702149/5000000000 : ℝ)|^4475 ≤ (7995465169567/25000000000000 : ℝ)^3451
        have hw : |(2075702149/5000000000 : ℝ)|=(2075702149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091323297/10000000000 : ℝ)|^4475 ≤ (21820124927401/100000000000000 : ℝ)^3451
        have hw : |(3091323297/10000000000 : ℝ)|=(3091323297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5512727049/10000000000 : ℝ)|^4475 ≤ (46198014387569/100000000000000 : ℝ)^3451
        have hw : |(5512727049/10000000000 : ℝ)|=(5512727049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1714224029/10000000000 : ℝ)*x 0 + (487315939/1000000000 : ℝ)*x 1 + (5901957119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1714224029/10000000000 : ℝ)^4475 ≤ (10157710505541/100000000000000 : ℝ)^3451 := by
    have hnat : (1714224029 : ℕ)^4475*100000000000000^3451 ≤ 10157710505541^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714224029 10000000000 10157710505541 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487315939/1000000000 : ℝ)^4475 ≤ (39370963068337/100000000000000 : ℝ)^3451 := by
    have hnat : (487315939 : ℕ)^4475*100000000000000^3451 ≤ 39370963068337^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487315939 1000000000 39370963068337 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5901957119/10000000000 : ℝ)^4475 ≤ (5047132640247/10000000000000 : ℝ)^3451 := by
    have hnat : (5901957119 : ℕ)^4475*10000000000000^3451 ≤ 5047132640247^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5901957119 10000000000 5047132640247 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1714224029/10000000000 : ℝ), (487315939/1000000000 : ℝ), (5901957119/10000000000 : ℝ)] ![(10157710505541/100000000000000 : ℝ), (39370963068337/100000000000000 : ℝ), (5047132640247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1714224029/10000000000 : ℝ)|^4475 ≤ (10157710505541/100000000000000 : ℝ)^3451
        have hw : |(-1714224029/10000000000 : ℝ)|=(1714224029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487315939/1000000000 : ℝ)|^4475 ≤ (39370963068337/100000000000000 : ℝ)^3451
        have hw : |(487315939/1000000000 : ℝ)|=(487315939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5901957119/10000000000 : ℝ)|^4475 ≤ (5047132640247/10000000000000 : ℝ)^3451
        have hw : |(5901957119/10000000000 : ℝ)|=(5901957119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518658097/1000000000 : ℝ)*x 0 + (-1264118881/10000000000 : ℝ)*x 1 + (1475489293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518658097/1000000000 : ℝ)^4475 ≤ (42685375655371/100000000000000 : ℝ)^3451 := by
    have hnat : (518658097 : ℕ)^4475*100000000000000^3451 ≤ 42685375655371^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518658097 1000000000 42685375655371 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264118881/10000000000 : ℝ)^4475 ≤ (273731893941/4000000000000 : ℝ)^3451 := by
    have hnat : (1264118881 : ℕ)^4475*4000000000000^3451 ≤ 273731893941^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264118881 10000000000 273731893941 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1475489293/2500000000 : ℝ)^4475 ≤ (50471326990193/100000000000000 : ℝ)^3451 := by
    have hnat : (1475489293 : ℕ)^4475*100000000000000^3451 ≤ 50471326990193^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475489293 2500000000 50471326990193 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518658097/1000000000 : ℝ), (-1264118881/10000000000 : ℝ), (1475489293/2500000000 : ℝ)] ![(42685375655371/100000000000000 : ℝ), (273731893941/4000000000000 : ℝ), (50471326990193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518658097/1000000000 : ℝ)|^4475 ≤ (42685375655371/100000000000000 : ℝ)^3451
        have hw : |(518658097/1000000000 : ℝ)|=(518658097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1264118881/10000000000 : ℝ)|^4475 ≤ (273731893941/4000000000000 : ℝ)^3451
        have hw : |(-1264118881/10000000000 : ℝ)|=(1264118881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1475489293/2500000000 : ℝ)|^4475 ≤ (50471326990193/100000000000000 : ℝ)^3451
        have hw : |(1475489293/2500000000 : ℝ)|=(1475489293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296645257/2500000000 : ℝ)*x 0 + (5901957047/10000000000 : ℝ)*x 1 + (-126411899/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296645257/2500000000 : ℝ)^4475 ≤ (10671344068587/25000000000000 : ℝ)^3451 := by
    have hnat : (1296645257 : ℕ)^4475*25000000000000^3451 ≤ 10671344068587^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296645257 2500000000 10671344068587 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5901957047/10000000000 : ℝ)^4475 ≤ (25235662802027/50000000000000 : ℝ)^3451 := by
    have hnat : (5901957047 : ℕ)^4475*50000000000000^3451 ≤ 25235662802027^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5901957047 10000000000 25235662802027 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126411899/1000000000 : ℝ)^4475 ≤ (1368659622737/20000000000000 : ℝ)^3451 := by
    have hnat : (126411899 : ℕ)^4475*20000000000000^3451 ≤ 1368659622737^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126411899 1000000000 1368659622737 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296645257/2500000000 : ℝ), (5901957047/10000000000 : ℝ), (-126411899/1000000000 : ℝ)] ![(10671344068587/25000000000000 : ℝ), (25235662802027/50000000000000 : ℝ), (1368659622737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296645257/2500000000 : ℝ)|^4475 ≤ (10671344068587/25000000000000 : ℝ)^3451
        have hw : |(1296645257/2500000000 : ℝ)|=(1296645257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5901957047/10000000000 : ℝ)|^4475 ≤ (25235662802027/50000000000000 : ℝ)^3451
        have hw : |(5901957047/10000000000 : ℝ)|=(5901957047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126411899/1000000000 : ℝ)|^4475 ≤ (1368659622737/20000000000000 : ℝ)^3451
        have hw : |(-126411899/1000000000 : ℝ)|=(126411899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s0_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103992693/250000000 : ℝ)*x 0 + (2725351621/5000000000 : ℝ)*x 1 + (3155575659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103992693/250000000 : ℝ)^4475 ≤ (8016208700923/25000000000000 : ℝ)^3451 := by
    have hnat : (103992693 : ℕ)^4475*25000000000000^3451 ≤ 8016208700923^3451*250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103992693 250000000 8016208700923 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725351621/5000000000 : ℝ)^4475 ≤ (1821005485131/4000000000000 : ℝ)^3451 := by
    have hnat : (2725351621 : ℕ)^4475*4000000000000^3451 ≤ 1821005485131^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725351621 5000000000 1821005485131 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3155575659/10000000000 : ℝ)^4475 ≤ (22410028058177/100000000000000 : ℝ)^3451 := by
    have hnat : (3155575659 : ℕ)^4475*100000000000000^3451 ≤ 22410028058177^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3155575659 10000000000 22410028058177 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103992693/250000000 : ℝ), (2725351621/5000000000 : ℝ), (3155575659/10000000000 : ℝ)] ![(8016208700923/25000000000000 : ℝ), (1821005485131/4000000000000 : ℝ), (22410028058177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103992693/250000000 : ℝ)|^4475 ≤ (8016208700923/25000000000000 : ℝ)^3451
        have hw : |(103992693/250000000 : ℝ)|=(103992693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725351621/5000000000 : ℝ)|^4475 ≤ (1821005485131/4000000000000 : ℝ)^3451
        have hw : |(2725351621/5000000000 : ℝ)|=(2725351621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3155575659/10000000000 : ℝ)|^4475 ≤ (22410028058177/100000000000000 : ℝ)^3451
        have hw : |(3155575659/10000000000 : ℝ)|=(3155575659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1263/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5157/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4473/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4473 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4473*1^1024 ≤ 0^1024*1^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4473/1024 : ℝ) ≤ (456743908282614259/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4473 ≤ (456743908282614259/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4473*25000000000000000000^1024 ≤ 456743908282614259^1024*5^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 456743908282614259 25000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (456743908282614259/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4473 := by
      have hnat : (1 : ℕ)^1024*1^4473 ≤ 1^4473*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25456743908282614259/25000000000000000000 : ℝ) ≤ (5020766666665999/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25456743908282614259/25000000000000000000 : ℝ)^1024 ≤ (5020766666665999/5000000000000000 : ℝ)^4473 := by
      have hnat : (25456743908282614259 : ℕ)^1024*5000000000000000^4473 ≤ 5020766666665999^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25456743908282614259 25000000000000000000 5020766666665999 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020766666665999/5000000000000000 : ℝ)) (X := (25456743908282614259/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12956743908282614259/12500000000000000000 : ℝ) ≤ (2520766666665999/2500000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (12956743908282614259/12500000000000000000 : ℝ)^1024 ≤ (2520766666665999/2500000000000000 : ℝ)^4473 := by
      have hnat : (12956743908282614259 : ℕ)^1024*2500000000000000^4473 ≤ 2520766666665999^4473*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12956743908282614259 12500000000000000000 2520766666665999 2500000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2520766666665999/2500000000000000 : ℝ)) (X := (12956743908282614259/12500000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20766666665999/2000000000000000 : ℝ)*(0 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20766666665999/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(456743908282614259/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20766666665999/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20766666665999/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5020766666665999/5000000000000000 : ℝ) by norm_num, show 1+(456743908282614259/25000000000000000000 : ℝ)+(0 : ℝ)=(25456743908282614259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(456743908282614259/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20766666665999/2000000000000000 : ℝ)*(2/5 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20766666665999/2000000000000000 : ℝ)*(2/5 : ℝ)=(2520766666665999/2500000000000000 : ℝ) by norm_num, show 1+2*(456743908282614259/25000000000000000000 : ℝ)=(12956743908282614259/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20766666665999/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20766666665999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20766666665999/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20766666665999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20766666665999/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20766666665999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1710502149/10000000000 : ℝ)*X 0 0+(5930758399/10000000000 : ℝ)*X 0 1+(1211339261/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5483002023/10000000000 : ℝ)*X 1 0+(-464143811/2000000000 : ℝ)*X 1 1+(96907141/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2741501007/5000000000 : ℝ)*X 2 0+(4845357073/10000000000 : ℝ)*X 2 1+(-2320719037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2075702149/5000000000 : ℝ)*X 0 0+(3091323297/10000000000 : ℝ)*X 0 1+(5512727049/10000000000 : ℝ)*X 0 2+(2075702149/5000000000 : ℝ)*X 1 0+(3091323297/10000000000 : ℝ)*X 1 1+(5512727049/10000000000 : ℝ)*X 1 2+(2075702149/5000000000 : ℝ)*X 2 0+(3091323297/10000000000 : ℝ)*X 2 1+(5512727049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1714224029/10000000000 : ℝ)*X 0 0+(487315939/1000000000 : ℝ)*X 0 1+(5901957119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518658097/1000000000 : ℝ)*X 1 0+(-1264118881/10000000000 : ℝ)*X 1 1+(1475489293/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296645257/2500000000 : ℝ)*X 2 0+(5901957047/10000000000 : ℝ)*X 2 1+(-126411899/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((103992693/250000000 : ℝ)*X 0 0+(2725351621/5000000000 : ℝ)*X 0 1+(3155575659/10000000000 : ℝ)*X 0 2+(103992693/250000000 : ℝ)*X 1 0+(2725351621/5000000000 : ℝ)*X 1 1+(3155575659/10000000000 : ℝ)*X 1 2+(103992693/250000000 : ℝ)*X 2 0+(2725351621/5000000000 : ℝ)*X 2 1+(3155575659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (710408184996058207515861/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17598239/25000000000000 : ℝ)*(base1) + (1587005649/100000000000000 : ℝ)*(base19) + (1585493349/100000000000000 : ℝ)*(base23) + (39371629/20000000000000 : ℝ)*(upper3) + (201269717/100000000000000 : ℝ)*(upper5) + (667158814582429/100000000000000 : ℝ)*(major0) + (667158814582429/100000000000000 : ℝ)*(major1) + (667158814582429/100000000000000 : ℝ)*(major2) + (230330855578029/25000000000000 : ℝ)*(sp0) + (115165915805673/12500000000000 : ℝ)*(sp1) + (230331831989421/25000000000000 : ℝ)*(sp2) + (103246484574171/25000000000000 : ℝ)*(sp3) + (2780765937/50000000000000 : ℝ)*(sp4) + (2470221449/100000000000000 : ℝ)*(sp7) + (412988478911089/100000000000000 : ℝ)*(f.failure) + (460664456725517/50000000000000 : ℝ)*(f.sum) + (51395148931571/100000000000000000000000000000 : ℝ)*base65 + (624763992868429/200000000000000000000000000000 : ℝ)*base68 + (734910493731571/200000000000000000000000000000 : ℝ)*base69 + (307335608331571/200000000000000000000000000000 : ℝ)*base71 + (284504471468429/100000000000000000000000000000 : ℝ)*base74 + (1039410275731571/200000000000000000000000000000 : ℝ)*base75 + (705782859531571/200000000000000000000000000000 : ℝ)*base77 + (519188049531571/200000000000000000000000000000 : ℝ)*base79 + (126996287231571/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (44787781/10000000000000000000000 : ℝ)*base90 + (44787781/10000000000000000000000 : ℝ)*base92 + (44787781/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3576602479311122379/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (392663717/50000000000000 : ℝ)*(base19) + (100040633/12500000000000 : ℝ)*(base23) + (21721191/25000000000000 : ℝ)*(base32) + (119230443/100000000000000 : ℝ)*(upper3) + (69286549/100000000000000 : ℝ)*(upper5) + (703856806712051/100000000000000 : ℝ)*(major0) + (703856806712051/100000000000000 : ℝ)*(major1) + (703856806712051/100000000000000 : ℝ)*(major2) + (491557169/25000000000000 : ℝ)*(sp1) + (2038457489/100000000000000 : ℝ)*(sp2) + (194401602711491/20000000000000 : ℝ)*(sp4) + (194401052400269/20000000000000 : ℝ)*(sp5) + (486002587387451/50000000000000 : ℝ)*(sp6) + (108926348440449/25000000000000 : ℝ)*(sp7) + (2723159254041/625000000000 : ℝ)*(f.failure) + (194401602711491/20000000000000 : ℝ)*(f.sum) + (97787492753949/100000000000000000000000000000 : ℝ)*base65 + (616566368853949/200000000000000000000000000000 : ℝ)*base67 + (1940193756546051/200000000000000000000000000000 : ℝ)*base70 + (537750878346051/200000000000000000000000000000 : ℝ)*base72 + (541662734553949/100000000000000000000000000000 : ℝ)*base73 + (802671755546051/200000000000000000000000000000 : ℝ)*base76 + (586576059146051/200000000000000000000000000000 : ℝ)*base78 + (77396040653949/200000000000000000000000000000 : ℝ)*base79 + (396356263846051/100000000000000000000000000000 : ℝ)*base82 + (129989/62500000000000000000 : ℝ)*base90 + (129989/62500000000000000000 : ℝ)*base92 + (129989/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1263/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5157/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1489_s1_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-187044209/1000000000 : ℝ)*x 0 + (44690309/80000000 : ℝ)*x 1 + (5087130073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187044209/1000000000 : ℝ)^4475 ≤ (11373954905311/100000000000000 : ℝ)^3451 := by
    have hnat : (187044209 : ℕ)^4475*100000000000000^3451 ≤ 11373954905311^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187044209 1000000000 11373954905311 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44690309/80000000 : ℝ)^4475 ≤ (5874872114571/12500000000000 : ℝ)^3451 := by
    have hnat : (44690309 : ℕ)^4475*12500000000000^3451 ≤ 5874872114571^3451*80000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44690309 80000000 5874872114571 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5087130073/10000000000 : ℝ)^4475 ≤ (41627068161777/100000000000000 : ℝ)^3451 := by
    have hnat : (5087130073 : ℕ)^4475*100000000000000^3451 ≤ 41627068161777^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087130073 10000000000 41627068161777 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187044209/1000000000 : ℝ), (44690309/80000000 : ℝ), (5087130073/10000000000 : ℝ)] ![(11373954905311/100000000000000 : ℝ), (5874872114571/12500000000000 : ℝ), (41627068161777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187044209/1000000000 : ℝ)|^4475 ≤ (11373954905311/100000000000000 : ℝ)^3451
        have hw : |(-187044209/1000000000 : ℝ)|=(187044209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44690309/80000000 : ℝ)|^4475 ≤ (5874872114571/12500000000000 : ℝ)^3451
        have hw : |(44690309/80000000 : ℝ)|=(44690309/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5087130073/10000000000 : ℝ)|^4475 ≤ (41627068161777/100000000000000 : ℝ)^3451
        have hw : |(5087130073/10000000000 : ℝ)|=(5087130073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336929323/625000000 : ℝ)*x 0 + (-2134062031/10000000000 : ℝ)*x 1 + (1271782361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336929323/625000000 : ℝ)^4475 ≤ (4487816485599/10000000000000 : ℝ)^3451 := by
    have hnat : (336929323 : ℕ)^4475*10000000000000^3451 ≤ 4487816485599^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336929323 625000000 4487816485599 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134062031/10000000000 : ℝ)^4475 ≤ (6747386817433/50000000000000 : ℝ)^3451 := by
    have hnat : (2134062031 : ℕ)^4475*50000000000000^3451 ≤ 6747386817433^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134062031 10000000000 6747386817433 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271782361/2500000000 : ℝ)^4475 ≤ (41627061487539/100000000000000 : ℝ)^3451 := by
    have hnat : (1271782361 : ℕ)^4475*100000000000000^3451 ≤ 41627061487539^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271782361 2500000000 41627061487539 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336929323/625000000 : ℝ), (-2134062031/10000000000 : ℝ), (1271782361/2500000000 : ℝ)] ![(4487816485599/10000000000000 : ℝ), (6747386817433/50000000000000 : ℝ), (41627061487539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336929323/625000000 : ℝ)|^4475 ≤ (4487816485599/10000000000000 : ℝ)^3451
        have hw : |(336929323/625000000 : ℝ)|=(336929323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134062031/10000000000 : ℝ)|^4475 ≤ (6747386817433/50000000000000 : ℝ)^3451
        have hw : |(-2134062031/10000000000 : ℝ)|=(2134062031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271782361/2500000000 : ℝ)|^4475 ≤ (41627061487539/100000000000000 : ℝ)^3451
        have hw : |(1271782361/2500000000 : ℝ)|=(1271782361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134771717/250000000 : ℝ)*x 0 + (635891217/1250000000 : ℝ)*x 1 + (-426812459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134771717/250000000 : ℝ)^4475 ≤ (44878159588009/100000000000000 : ℝ)^3451 := by
    have hnat : (134771717 : ℕ)^4475*100000000000000^3451 ≤ 44878159588009^3451*250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134771717 250000000 44878159588009 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635891217/1250000000 : ℝ)^4475 ≤ (20813532292957/50000000000000 : ℝ)^3451 := by
    have hnat : (635891217 : ℕ)^4475*50000000000000^3451 ≤ 20813532292957^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635891217 1250000000 20813532292957 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426812459/2000000000 : ℝ)^4475 ≤ (1349477579963/10000000000000 : ℝ)^3451 := by
    have hnat : (426812459 : ℕ)^4475*10000000000000^3451 ≤ 1349477579963^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426812459 2000000000 1349477579963 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134771717/250000000 : ℝ), (635891217/1250000000 : ℝ), (-426812459/2000000000 : ℝ)] ![(44878159588009/100000000000000 : ℝ), (20813532292957/50000000000000 : ℝ), (1349477579963/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134771717/250000000 : ℝ)|^4475 ≤ (44878159588009/100000000000000 : ℝ)^3451
        have hw : |(134771717/250000000 : ℝ)|=(134771717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635891217/1250000000 : ℝ)|^4475 ≤ (20813532292957/50000000000000 : ℝ)^3451
        have hw : |(635891217/1250000000 : ℝ)|=(635891217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426812459/2000000000 : ℝ)|^4475 ≤ (1349477579963/10000000000000 : ℝ)^3451
        have hw : |(-426812459/2000000000 : ℝ)|=(426812459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128996793/5000000000 : ℝ)*x 0 + (3732533133/10000000000 : ℝ)*x 1 + (1211524537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128996793/5000000000 : ℝ)^4475 ≤ (33050698304567/100000000000000 : ℝ)^3451 := by
    have hnat : (2128996793 : ℕ)^4475*100000000000000^3451 ≤ 33050698304567^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128996793 5000000000 33050698304567 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3732533133/10000000000 : ℝ)^4475 ≤ (217668828669/781250000000 : ℝ)^3451 := by
    have hnat : (3732533133 : ℕ)^4475*781250000000^3451 ≤ 217668828669^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732533133 10000000000 217668828669 781250000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211524537/2500000000 : ℝ)^4475 ≤ (39087691617031/100000000000000 : ℝ)^3451 := by
    have hnat : (1211524537 : ℕ)^4475*100000000000000^3451 ≤ 39087691617031^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211524537 2500000000 39087691617031 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128996793/5000000000 : ℝ), (3732533133/10000000000 : ℝ), (1211524537/2500000000 : ℝ)] ![(33050698304567/100000000000000 : ℝ), (217668828669/781250000000 : ℝ), (39087691617031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128996793/5000000000 : ℝ)|^4475 ≤ (33050698304567/100000000000000 : ℝ)^3451
        have hw : |(2128996793/5000000000 : ℝ)|=(2128996793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3732533133/10000000000 : ℝ)|^4475 ≤ (217668828669/781250000000 : ℝ)^3451
        have hw : |(3732533133/10000000000 : ℝ)|=(3732533133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1211524537/2500000000 : ℝ)|^4475 ≤ (39087691617031/100000000000000 : ℝ)^3451
        have hw : |(1211524537/2500000000 : ℝ)|=(1211524537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-935395581/5000000000 : ℝ)*x 0 + (203715851/400000000 : ℝ)*x 1 + (5580426207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935395581/5000000000 : ℝ)^4475 ≤ (11376707500549/100000000000000 : ℝ)^3451 := by
    have hnat : (935395581 : ℕ)^4475*100000000000000^3451 ≤ 11376707500549^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935395581 5000000000 11376707500549 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203715851/400000000 : ℝ)^4475 ≤ (20844131438869/50000000000000 : ℝ)^3451 := by
    have hnat : (203715851 : ℕ)^4475*50000000000000^3451 ≤ 20844131438869^3451*400000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203715851 400000000 20844131438869 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5580426207/10000000000 : ℝ)^4475 ≤ (5866878701281/12500000000000 : ℝ)^3451 := by
    have hnat : (5580426207 : ℕ)^4475*12500000000000^3451 ≤ 5866878701281^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5580426207 10000000000 5866878701281 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935395581/5000000000 : ℝ), (203715851/400000000 : ℝ), (5580426207/10000000000 : ℝ)] ![(11376707500549/100000000000000 : ℝ), (20844131438869/50000000000000 : ℝ), (5866878701281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935395581/5000000000 : ℝ)|^4475 ≤ (11376707500549/100000000000000 : ℝ)^3451
        have hw : |(-935395581/5000000000 : ℝ)|=(935395581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203715851/400000000 : ℝ)|^4475 ≤ (20844131438869/50000000000000 : ℝ)^3451
        have hw : |(203715851/400000000 : ℝ)|=(203715851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5580426207/10000000000 : ℝ)|^4475 ≤ (5866878701281/12500000000000 : ℝ)^3451
        have hw : |(5580426207/10000000000 : ℝ)|=(5580426207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259769731/10000000000 : ℝ)*x 0 + (-1640765303/10000000000 : ℝ)*x 1 + (5580426277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259769731/10000000000 : ℝ)^4475 ≤ (8693615268293/20000000000000 : ℝ)^3451 := by
    have hnat : (5259769731 : ℕ)^4475*20000000000000^3451 ≤ 8693615268293^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259769731 10000000000 8693615268293 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1640765303/10000000000 : ℝ)^4475 ≤ (149951457301/1562500000000 : ℝ)^3451 := by
    have hnat : (1640765303 : ℕ)^4475*1562500000000^3451 ≤ 149951457301^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640765303 10000000000 149951457301 1562500000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5580426277/10000000000 : ℝ)^4475 ≤ (46935030373689/100000000000000 : ℝ)^3451 := by
    have hnat : (5580426277 : ℕ)^4475*100000000000000^3451 ≤ 46935030373689^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5580426277 10000000000 46935030373689 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259769731/10000000000 : ℝ), (-1640765303/10000000000 : ℝ), (5580426277/10000000000 : ℝ)] ![(8693615268293/20000000000000 : ℝ), (149951457301/1562500000000 : ℝ), (46935030373689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259769731/10000000000 : ℝ)|^4475 ≤ (8693615268293/20000000000000 : ℝ)^3451
        have hw : |(5259769731/10000000000 : ℝ)|=(5259769731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1640765303/10000000000 : ℝ)|^4475 ≤ (149951457301/1562500000000 : ℝ)^3451
        have hw : |(-1640765303/10000000000 : ℝ)|=(1640765303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5580426277/10000000000 : ℝ)|^4475 ≤ (46935030373689/100000000000000 : ℝ)^3451
        have hw : |(5580426277/10000000000 : ℝ)|=(5580426277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259769703/10000000000 : ℝ)*x 0 + (5580426267/10000000000 : ℝ)*x 1 + (-820382679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259769703/10000000000 : ℝ)^4475 ≤ (10867019010351/25000000000000 : ℝ)^3451 := by
    have hnat : (5259769703 : ℕ)^4475*25000000000000^3451 ≤ 10867019010351^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259769703 10000000000 10867019010351 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5580426267/10000000000 : ℝ)^4475 ≤ (23467515132313/50000000000000 : ℝ)^3451 := by
    have hnat : (5580426267 : ℕ)^4475*50000000000000^3451 ≤ 23467515132313^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5580426267 10000000000 23467515132313 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820382679/5000000000 : ℝ)^4475 ≤ (149951463819/1562500000000 : ℝ)^3451 := by
    have hnat : (820382679 : ℕ)^4475*1562500000000^3451 ≤ 149951463819^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820382679 5000000000 149951463819 1562500000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259769703/10000000000 : ℝ), (5580426267/10000000000 : ℝ), (-820382679/5000000000 : ℝ)] ![(10867019010351/25000000000000 : ℝ), (23467515132313/50000000000000 : ℝ), (149951463819/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259769703/10000000000 : ℝ)|^4475 ≤ (10867019010351/25000000000000 : ℝ)^3451
        have hw : |(5259769703/10000000000 : ℝ)|=(5259769703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5580426267/10000000000 : ℝ)|^4475 ≤ (23467515132313/50000000000000 : ℝ)^3451
        have hw : |(5580426267/10000000000 : ℝ)|=(5580426267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-820382679/5000000000 : ℝ)|^4475 ≤ (149951463819/1562500000000 : ℝ)^3451
        have hw : |(-820382679/5000000000 : ℝ)|=(820382679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s1_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851754401/2000000000 : ℝ)*x 0 + (2416617221/5000000000 : ℝ)*x 1 + (468201411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851754401/2000000000 : ℝ)^4475 ≤ (16529266741793/50000000000000 : ℝ)^3451 := by
    have hnat : (851754401 : ℕ)^4475*50000000000000^3451 ≤ 16529266741793^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851754401 2000000000 16529266741793 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416617221/5000000000 : ℝ)^4475 ≤ (2434575084893/6250000000000 : ℝ)^3451 := by
    have hnat : (2416617221 : ℕ)^4475*6250000000000^3451 ≤ 2434575084893^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416617221 5000000000 2434575084893 6250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468201411/1250000000 : ℝ)^4475 ≤ (27988265150879/100000000000000 : ℝ)^3451 := by
    have hnat : (468201411 : ℕ)^4475*100000000000000^3451 ≤ 27988265150879^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468201411 1250000000 27988265150879 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851754401/2000000000 : ℝ), (2416617221/5000000000 : ℝ), (468201411/1250000000 : ℝ)] ![(16529266741793/50000000000000 : ℝ), (2434575084893/6250000000000 : ℝ), (27988265150879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851754401/2000000000 : ℝ)|^4475 ≤ (16529266741793/50000000000000 : ℝ)^3451
        have hw : |(851754401/2000000000 : ℝ)|=(851754401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2416617221/5000000000 : ℝ)|^4475 ≤ (2434575084893/6250000000000 : ℝ)^3451
        have hw : |(2416617221/5000000000 : ℝ)|=(2416617221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468201411/1250000000 : ℝ)|^4475 ≤ (27988265150879/100000000000000 : ℝ)^3451
        have hw : |(468201411/1250000000 : ℝ)|=(468201411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5157/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1859/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5157/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1263/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5157/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1263/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5157/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1263/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5157/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1263/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5157/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1263/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5157/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1263/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1263/50000 : ℝ) ^ (4473/1024 : ℝ) ≤ (10509129785321/100000000000000000000 : ℝ) := by
    have hpowers : (1263/50000 : ℝ)^4473 ≤ (10509129785321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1263 : ℕ)^4473*100000000000000000000^1024 ≤ 10509129785321^1024*50000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1263 50000 10509129785321 100000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1263/50000 : ℝ)) (X := (10509129785321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5157/20000 : ℝ) ^ (4473/1024 : ℝ) ≤ (134191522615967829/50000000000000000000 : ℝ) := by
    have hpowers : (5157/20000 : ℝ)^4473 ≤ (134191522615967829/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5157 : ℕ)^4473*50000000000000000000^1024 ≤ 134191522615967829^1024*20000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5157 20000 134191522615967829 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5157/20000 : ℝ)) (X := (134191522615967829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000010509129785321/50000000000000000000 : ℝ) ≤ (200000009623383/200000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (50000010509129785321/50000000000000000000 : ℝ)^1024 ≤ (200000009623383/200000000000000 : ℝ)^4473 := by
      have hnat : (50000010509129785321 : ℕ)^1024*200000000000000^4473 ≤ 200000009623383^4473*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000010509129785321 50000000000000000000 200000009623383 200000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000009623383/200000000000000 : ℝ)) (X := (50000010509129785321/50000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100268393554361720979/100000000000000000000 : ℝ) ≤ (2501534490628763/2500000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (100268393554361720979/100000000000000000000 : ℝ)^1024 ≤ (2501534490628763/2500000000000000 : ℝ)^4473 := by
      have hnat : (100268393554361720979 : ℕ)^1024*2500000000000000^4473 ≤ 2501534490628763^4473*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100268393554361720979 100000000000000000000 2501534490628763 2500000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501534490628763/2500000000000000 : ℝ)) (X := (100268393554361720979/100000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25134191522615967829/25000000000000000000 : ℝ) ≤ (5006137721930477/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25134191522615967829/25000000000000000000 : ℝ)^1024 ≤ (5006137721930477/5000000000000000 : ℝ)^4473 := by
      have hnat : (25134191522615967829 : ℕ)^1024*5000000000000000^4473 ≤ 5006137721930477^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25134191522615967829 25000000000000000000 5006137721930477 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006137721930477/5000000000000000 : ℝ)) (X := (25134191522615967829/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10509129785321/100000000000000000000 : ℝ) ≤ ((38759834105958960491/38765000000000000000 : ℝ)+2*(3068740672951/1162950000000000 : ℝ)*(1263/50000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (38759834105958960491/38765000000000000000 : ℝ)+2*(3068740672951/1162950000000000 : ℝ)*(1263/50000 : ℝ)=(200000009623383/200000000000000 : ℝ) by norm_num, show 1+2*(10509129785321/100000000000000000000 : ℝ)=(50000010509129785321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(134191522615967829/50000000000000000000 : ℝ)+(10509129785321/100000000000000000000 : ℝ) ≤ ((38759834105958960491/38765000000000000000 : ℝ)+(3068740672951/1162950000000000 : ℝ)*((5157/20000 : ℝ)+(1263/50000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (38759834105958960491/38765000000000000000 : ℝ)+(3068740672951/1162950000000000 : ℝ)*((5157/20000 : ℝ)+(1263/50000 : ℝ))=(2501534490628763/2500000000000000 : ℝ) by norm_num, show 1+(134191522615967829/50000000000000000000 : ℝ)+(10509129785321/100000000000000000000 : ℝ)=(100268393554361720979/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(134191522615967829/50000000000000000000 : ℝ) ≤ ((38759834105958960491/38765000000000000000 : ℝ)+2*(3068740672951/1162950000000000 : ℝ)*(5157/20000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (38759834105958960491/38765000000000000000 : ℝ)+2*(3068740672951/1162950000000000 : ℝ)*(5157/20000 : ℝ)=(5006137721930477/5000000000000000 : ℝ) by norm_num, show 1+2*(134191522615967829/50000000000000000000 : ℝ)=(25134191522615967829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38759834105958960491/38765000000000000000 : ℝ)*(X 1 0+X 2 0)+(3068740672951/1162950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1263/50000 : ℝ)) (hi := (5157/20000 : ℝ)) (c := (38759834105958960491/38765000000000000000 : ℝ)) (alpha := (3068740672951/1162950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38759834105958960491/38765000000000000000 : ℝ)*(X 0 1+X 2 1)+(3068740672951/1162950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1263/50000 : ℝ)) (hi := (5157/20000 : ℝ)) (c := (38759834105958960491/38765000000000000000 : ℝ)) (alpha := (3068740672951/1162950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38759834105958960491/38765000000000000000 : ℝ)*(X 0 2+X 1 2)+(3068740672951/1162950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (1263/50000 : ℝ)) (hi := (5157/20000 : ℝ)) (c := (38759834105958960491/38765000000000000000 : ℝ)) (alpha := (3068740672951/1162950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-187044209/1000000000 : ℝ)*X 0 0+(44690309/80000000 : ℝ)*X 0 1+(5087130073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((336929323/625000000 : ℝ)*X 1 0+(-2134062031/10000000000 : ℝ)*X 1 1+(1271782361/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134771717/250000000 : ℝ)*X 2 0+(635891217/1250000000 : ℝ)*X 2 1+(-426812459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2128996793/5000000000 : ℝ)*X 0 0+(3732533133/10000000000 : ℝ)*X 0 1+(1211524537/2500000000 : ℝ)*X 0 2+(2128996793/5000000000 : ℝ)*X 1 0+(3732533133/10000000000 : ℝ)*X 1 1+(1211524537/2500000000 : ℝ)*X 1 2+(2128996793/5000000000 : ℝ)*X 2 0+(3732533133/10000000000 : ℝ)*X 2 1+(1211524537/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-935395581/5000000000 : ℝ)*X 0 0+(203715851/400000000 : ℝ)*X 0 1+(5580426207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259769731/10000000000 : ℝ)*X 1 0+(-1640765303/10000000000 : ℝ)*X 1 1+(5580426277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259769703/10000000000 : ℝ)*X 2 0+(5580426267/10000000000 : ℝ)*X 2 1+(-820382679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851754401/2000000000 : ℝ)*X 0 0+(2416617221/5000000000 : ℝ)*X 0 1+(468201411/1250000000 : ℝ)*X 0 2+(851754401/2000000000 : ℝ)*X 1 0+(2416617221/5000000000 : ℝ)*X 1 1+(468201411/1250000000 : ℝ)*X 1 2+(851754401/2000000000 : ℝ)*X 2 0+(2416617221/5000000000 : ℝ)*X 2 1+(468201411/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78667483623200980373677813/19382500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37293327/50000000000000 : ℝ)*(base1) + (69578461/10000000000000 : ℝ)*(base19) + (254045533/50000000000000 : ℝ)*(base23) + (135998443/100000000000000 : ℝ)*(upper3) + (29013944277919/2000000000000 : ℝ)*(major0) + (29013944277919/2000000000000 : ℝ)*(major1) + (29013944277919/2000000000000 : ℝ)*(major2) + (1001687300901329/50000000000000 : ℝ)*(sp0) + (1001687340166801/50000000000000 : ℝ)*(sp1) + (1001687303637273/50000000000000 : ℝ)*(sp2) + (449008756664583/50000000000000 : ℝ)*(sp3) + (13264097/1562500000000 : ℝ)*(sp4) + (260752599/100000000000000 : ℝ)*(sp6) + (53138733/4000000000000 : ℝ)*(sp7) + (179603783276829/20000000000000 : ℝ)*(f.failure) + (500843844029553/25000000000000 : ℝ)*(f.sum) + (5353616267653/4651800000000000000000000000 : ℝ)*base65 + (956614392299974687/232590000000000000000000000000000 : ℝ)*base67 + (315766662817225313/232590000000000000000000000000000 : ℝ)*base70 + (1873784943965164687/232590000000000000000000000000000 : ℝ)*base71 + (3320934587357/11629500000000000000000000000 : ℝ)*base74 + (1021561131109954687/232590000000000000000000000000000 : ℝ)*base75 + (2009816544950974687/232590000000000000000000000000000 : ℝ)*base77 + (2892233643021964687/232590000000000000000000000000000 : ℝ)*base79 + (33486266307631/5814750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4313759/2000000000000000000000 : ℝ)*base89 + (4313759/2000000000000000000000 : ℝ)*base91 + (4313759/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36953210347401467510508977/19382500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78232727/20000000000000 : ℝ)*(base19) + (39370321/10000000000000 : ℝ)*(base23) + (13182647/20000000000000 : ℝ)*(upper3) + (3288779/100000000000000 : ℝ)*(lower4) + (717231/6250000000000 : ℝ)*(upper5) + (14852958743617/1000000000000 : ℝ)*(major0) + (14852958743617/1000000000000 : ℝ)*(major1) + (14852958743617/1000000000000 : ℝ)*(major2) + (614855481/25000000000000 : ℝ)*(sp1) + (1374270653/50000000000000 : ℝ)*(sp2) + (2051155307389749/100000000000000 : ℝ)*(sp4) + (205115245680419/10000000000000 : ℝ)*(sp5) + (2051152165145233/100000000000000 : ℝ)*(sp6) + (919436377782829/100000000000000 : ℝ)*(sp7) + (919436377782829/100000000000000 : ℝ)*(f.failure) + (2051155307389749/100000000000000 : ℝ)*(f.sum) + (43545398096333/23259000000000000000000000000 : ℝ)*base66 + (239367638382072841/116295000000000000000000000000000 : ℝ)*base67 + (552161136151482841/116295000000000000000000000000000 : ℝ)*base69 + (13879439800242841/116295000000000000000000000000000 : ℝ)*base71 + (18836876668711/5814750000000000000000000000 : ℝ)*base73 + (780508829104797841/116295000000000000000000000000000 : ℝ)*base75 + (411706055859927841/116295000000000000000000000000000 : ℝ)*base77 + (724942821441732841/116295000000000000000000000000000 : ℝ)*base79 + (14763825341767/5814750000000000000000000000 : ℝ)*base81 + (71160241/10000000000000000000000 : ℝ)*base90 + (71160241/10000000000000000000000 : ℝ)*base92 + (71160241/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5157/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1859/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1489_s2_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-948865247/5000000000 : ℝ)*x 0 + (683207359/1250000000 : ℝ)*x 1 + (5190127283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948865247/5000000000 : ℝ)^4475 ≤ (463583795371/4000000000000 : ℝ)^3451 := by
    have hnat : (948865247 : ℕ)^4475*4000000000000^3451 ≤ 463583795371^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948865247 5000000000 463583795371 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683207359/1250000000 : ℝ)^4475 ≤ (2855448708681/6250000000000 : ℝ)^3451 := by
    have hnat : (683207359 : ℕ)^4475*6250000000000^3451 ≤ 2855448708681^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683207359 1250000000 2855448708681 6250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190127283/10000000000 : ℝ)^4475 ≤ (8544645152913/20000000000000 : ℝ)^3451 := by
    have hnat : (5190127283 : ℕ)^4475*20000000000000^3451 ≤ 8544645152913^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190127283 10000000000 8544645152913 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948865247/5000000000 : ℝ), (683207359/1250000000 : ℝ), (5190127283/10000000000 : ℝ)] ![(463583795371/4000000000000 : ℝ), (2855448708681/6250000000000 : ℝ), (8544645152913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948865247/5000000000 : ℝ)|^4475 ≤ (463583795371/4000000000000 : ℝ)^3451
        have hw : |(-948865247/5000000000 : ℝ)|=(948865247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683207359/1250000000 : ℝ)|^4475 ≤ (2855448708681/6250000000000 : ℝ)^3451
        have hw : |(683207359/1250000000 : ℝ)|=(683207359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190127283/10000000000 : ℝ)|^4475 ≤ (8544645152913/20000000000000 : ℝ)^3451
        have hw : |(5190127283/10000000000 : ℝ)|=(5190127283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360446649/10000000000 : ℝ)*x 0 + (-2039774477/10000000000 : ℝ)*x 1 + (5190126951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360446649/10000000000 : ℝ)^4475 ≤ (44550027786063/100000000000000 : ℝ)^3451 := by
    have hnat : (5360446649 : ℕ)^4475*100000000000000^3451 ≤ 44550027786063^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360446649 10000000000 44550027786063 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039774477/10000000000 : ℝ)^4475 ≤ (12726749987/100000000000 : ℝ)^3451 := by
    have hnat : (2039774477 : ℕ)^4475*100000000000^3451 ≤ 12726749987^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039774477 10000000000 12726749987 100000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190126951/10000000000 : ℝ)^4475 ≤ (2136161111037/5000000000000 : ℝ)^3451 := by
    have hnat : (5190126951 : ℕ)^4475*5000000000000^3451 ≤ 2136161111037^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190126951 10000000000 2136161111037 5000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360446649/10000000000 : ℝ), (-2039774477/10000000000 : ℝ), (5190126951/10000000000 : ℝ)] ![(44550027786063/100000000000000 : ℝ), (12726749987/100000000000 : ℝ), (2136161111037/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360446649/10000000000 : ℝ)|^4475 ≤ (44550027786063/100000000000000 : ℝ)^3451
        have hw : |(5360446649/10000000000 : ℝ)|=(5360446649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039774477/10000000000 : ℝ)|^4475 ≤ (12726749987/100000000000 : ℝ)^3451
        have hw : |(-2039774477/10000000000 : ℝ)|=(2039774477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190126951/10000000000 : ℝ)|^4475 ≤ (2136161111037/5000000000000 : ℝ)^3451
        have hw : |(5190126951/10000000000 : ℝ)|=(5190126951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360446729/10000000000 : ℝ)*x 0 + (5190126649/10000000000 : ℝ)*x 1 + (-127485923/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360446729/10000000000 : ℝ)^4475 ≤ (44550028648217/100000000000000 : ℝ)^3451 := by
    have hnat : (5360446729 : ℕ)^4475*100000000000000^3451 ≤ 44550028648217^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360446729 10000000000 44550028648217 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190126649/10000000000 : ℝ)^4475 ≤ (42723218997141/100000000000000 : ℝ)^3451 := by
    have hnat : (5190126649 : ℕ)^4475*100000000000000^3451 ≤ 42723218997141^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190126649 10000000000 42723218997141 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127485923/625000000 : ℝ)^4475 ≤ (636337617069/5000000000000 : ℝ)^3451 := by
    have hnat : (127485923 : ℕ)^4475*5000000000000^3451 ≤ 636337617069^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127485923 625000000 636337617069 5000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360446729/10000000000 : ℝ), (5190126649/10000000000 : ℝ), (-127485923/625000000 : ℝ)] ![(44550028648217/100000000000000 : ℝ), (42723218997141/100000000000000 : ℝ), (636337617069/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360446729/10000000000 : ℝ)|^4475 ≤ (44550028648217/100000000000000 : ℝ)^3451
        have hw : |(5360446729/10000000000 : ℝ)|=(5360446729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190126649/10000000000 : ℝ)|^4475 ≤ (42723218997141/100000000000000 : ℝ)^3451
        have hw : |(5190126649/10000000000 : ℝ)|=(5190126649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127485923/625000000 : ℝ)|^4475 ≤ (636337617069/5000000000000 : ℝ)^3451
        have hw : |(-127485923/625000000 : ℝ)|=(127485923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85550033/200000000 : ℝ)*x 0 + (795941431/2000000000 : ℝ)*x 1 + (459438657/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85550033/200000000 : ℝ)^4475 ≤ (2077949049077/6250000000000 : ℝ)^3451 := by
    have hnat : (85550033 : ℕ)^4475*6250000000000^3451 ≤ 2077949049077^3451*200000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85550033 200000000 2077949049077 6250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795941431/2000000000 : ℝ)^4475 ≤ (75693173209/250000000000 : ℝ)^3451 := by
    have hnat : (795941431 : ℕ)^4475*250000000000^3451 ≤ 75693173209^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795941431 2000000000 75693173209 250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459438657/1000000000 : ℝ)^4475 ≤ (36475545915561/100000000000000 : ℝ)^3451 := by
    have hnat : (459438657 : ℕ)^4475*100000000000000^3451 ≤ 36475545915561^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459438657 1000000000 36475545915561 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85550033/200000000 : ℝ), (795941431/2000000000 : ℝ), (459438657/1000000000 : ℝ)] ![(2077949049077/6250000000000 : ℝ), (75693173209/250000000000 : ℝ), (36475545915561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85550033/200000000 : ℝ)|^4475 ≤ (2077949049077/6250000000000 : ℝ)^3451
        have hw : |(85550033/200000000 : ℝ)|=(85550033/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795941431/2000000000 : ℝ)|^4475 ≤ (75693173209/250000000000 : ℝ)^3451
        have hw : |(795941431/2000000000 : ℝ)|=(795941431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459438657/1000000000 : ℝ)|^4475 ≤ (36475545915561/100000000000000 : ℝ)^3451
        have hw : |(459438657/1000000000 : ℝ)|=(459438657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897787703/10000000000 : ℝ)*x 0 + (5191895453/10000000000 : ℝ)*x 1 + (2731937831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897787703/10000000000 : ℝ)^4475 ≤ (2897511984081/25000000000000 : ℝ)^3451 := by
    have hnat : (1897787703 : ℕ)^4475*25000000000000^3451 ≤ 2897511984081^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897787703 10000000000 2897511984081 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191895453/10000000000 : ℝ)^4475 ≤ (8548420093059/20000000000000 : ℝ)^3451 := by
    have hnat : (5191895453 : ℕ)^4475*20000000000000^3451 ≤ 8548420093059^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191895453 10000000000 8548420093059 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731937831/5000000000 : ℝ)^4475 ≤ (22833925792857/50000000000000 : ℝ)^3451 := by
    have hnat : (2731937831 : ℕ)^4475*50000000000000^3451 ≤ 22833925792857^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731937831 5000000000 22833925792857 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897787703/10000000000 : ℝ), (5191895453/10000000000 : ℝ), (2731937831/5000000000 : ℝ)] ![(2897511984081/25000000000000 : ℝ), (8548420093059/20000000000000 : ℝ), (22833925792857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897787703/10000000000 : ℝ)|^4475 ≤ (2897511984081/25000000000000 : ℝ)^3451
        have hw : |(-1897787703/10000000000 : ℝ)|=(1897787703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191895453/10000000000 : ℝ)|^4475 ≤ (8548420093059/20000000000000 : ℝ)^3451
        have hw : |(5191895453/10000000000 : ℝ)|=(5191895453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731937831/5000000000 : ℝ)|^4475 ≤ (22833925792857/50000000000000 : ℝ)^3451
        have hw : |(2731937831/5000000000 : ℝ)|=(2731937831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288350807/10000000000 : ℝ)*x 0 + (-1766025721/10000000000 : ℝ)*x 1 + (2731938779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288350807/10000000000 : ℝ)^4475 ≤ (21887305604859/50000000000000 : ℝ)^3451 := by
    have hnat : (5288350807 : ℕ)^4475*50000000000000^3451 ≤ 21887305604859^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288350807 10000000000 21887305604859 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1766025721/10000000000 : ℝ)^4475 ≤ (2639379160863/25000000000000 : ℝ)^3451 := by
    have hnat : (1766025721 : ℕ)^4475*25000000000000^3451 ≤ 2639379160863^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766025721 10000000000 2639379160863 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731938779/5000000000 : ℝ)^4475 ≤ (1826714885399/4000000000000 : ℝ)^3451 := by
    have hnat : (2731938779 : ℕ)^4475*4000000000000^3451 ≤ 1826714885399^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731938779 5000000000 1826714885399 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288350807/10000000000 : ℝ), (-1766025721/10000000000 : ℝ), (2731938779/5000000000 : ℝ)] ![(21887305604859/50000000000000 : ℝ), (2639379160863/25000000000000 : ℝ), (1826714885399/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288350807/10000000000 : ℝ)|^4475 ≤ (21887305604859/50000000000000 : ℝ)^3451
        have hw : |(5288350807/10000000000 : ℝ)|=(5288350807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1766025721/10000000000 : ℝ)|^4475 ≤ (2639379160863/25000000000000 : ℝ)^3451
        have hw : |(-1766025721/10000000000 : ℝ)|=(1766025721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731938779/5000000000 : ℝ)|^4475 ≤ (1826714885399/4000000000000 : ℝ)^3451
        have hw : |(2731938779/5000000000 : ℝ)|=(2731938779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288352527/10000000000 : ℝ)*x 0 + (5463874807/10000000000 : ℝ)*x 1 + (-883013593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288352527/10000000000 : ℝ)^4475 ≤ (1367957177241/3125000000000 : ℝ)^3451 := by
    have hnat : (5288352527 : ℕ)^4475*3125000000000^3451 ≤ 1367957177241^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288352527 10000000000 1367957177241 3125000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463874807/10000000000 : ℝ)^4475 ≤ (22833921159519/50000000000000 : ℝ)^3451 := by
    have hnat : (5463874807 : ℕ)^4475*50000000000000^3451 ≤ 22833921159519^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463874807 10000000000 22833921159519 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883013593/5000000000 : ℝ)^4475 ≤ (10557528000109/100000000000000 : ℝ)^3451 := by
    have hnat : (883013593 : ℕ)^4475*100000000000000^3451 ≤ 10557528000109^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883013593 5000000000 10557528000109 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288352527/10000000000 : ℝ), (5463874807/10000000000 : ℝ), (-883013593/5000000000 : ℝ)] ![(1367957177241/3125000000000 : ℝ), (22833921159519/50000000000000 : ℝ), (10557528000109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288352527/10000000000 : ℝ)|^4475 ≤ (1367957177241/3125000000000 : ℝ)^3451
        have hw : |(5288352527/10000000000 : ℝ)|=(5288352527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463874807/10000000000 : ℝ)|^4475 ≤ (22833921159519/50000000000000 : ℝ)^3451
        have hw : |(5463874807/10000000000 : ℝ)|=(5463874807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883013593/5000000000 : ℝ)|^4475 ≤ (10557528000109/100000000000000 : ℝ)^3451
        have hw : |(-883013593/5000000000 : ℝ)|=(883013593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s2_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138817743/5000000000 : ℝ)*x 0 + (1147611927/2500000000 : ℝ)*x 1 + (3983679667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138817743/5000000000 : ℝ)^4475 ≤ (16624266855011/50000000000000 : ℝ)^3451 := by
    have hnat : (2138817743 : ℕ)^4475*50000000000000^3451 ≤ 16624266855011^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138817743 5000000000 16624266855011 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147611927/2500000000 : ℝ)^4475 ≤ (36435000863911/100000000000000 : ℝ)^3451 := by
    have hnat : (1147611927 : ℕ)^4475*100000000000000^3451 ≤ 36435000863911^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147611927 2500000000 36435000863911 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983679667/10000000000 : ℝ)^4475 ≤ (30316465412981/100000000000000 : ℝ)^3451 := by
    have hnat : (3983679667 : ℕ)^4475*100000000000000^3451 ≤ 30316465412981^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983679667 10000000000 30316465412981 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138817743/5000000000 : ℝ), (1147611927/2500000000 : ℝ), (3983679667/10000000000 : ℝ)] ![(16624266855011/50000000000000 : ℝ), (36435000863911/100000000000000 : ℝ), (30316465412981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138817743/5000000000 : ℝ)|^4475 ≤ (16624266855011/50000000000000 : ℝ)^3451
        have hw : |(2138817743/5000000000 : ℝ)|=(2138817743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147611927/2500000000 : ℝ)|^4475 ≤ (36435000863911/100000000000000 : ℝ)^3451
        have hw : |(1147611927/2500000000 : ℝ)|=(1147611927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983679667/10000000000 : ℝ)|^4475 ≤ (30316465412981/100000000000000 : ℝ)^3451
        have hw : |(3983679667/10000000000 : ℝ)|=(3983679667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1859/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10261/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1609/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1859/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1859/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1859/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1859/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1859/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1859/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8037/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (824595242803031/50000000000000000000 : ℝ) := by
    have hpowers : (8037/100000 : ℝ)^4473 ≤ (824595242803031/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8037 : ℕ)^4473*50000000000000000000^1024 ≤ 824595242803031^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8037 100000 824595242803031 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8037/100000 : ℝ)) (X := (824595242803031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1859/10000 : ℝ) ^ (4473/1024 : ℝ) ≤ (64282460358302779/100000000000000000000 : ℝ) := by
    have hpowers : (1859/10000 : ℝ)^4473 ≤ (64282460358302779/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1859 : ℕ)^4473*100000000000000000000^1024 ≤ 64282460358302779^1024*10000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1859 10000 64282460358302779 100000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1859/10000 : ℝ)) (X := (64282460358302779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000824595242803031/25000000000000000000 : ℝ) ≤ (5000037754294267/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25000824595242803031/25000000000000000000 : ℝ)^1024 ≤ (5000037754294267/5000000000000000 : ℝ)^4473 := by
      have hnat : (25000824595242803031 : ℕ)^1024*5000000000000000^4473 ≤ 5000037754294267^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000824595242803031 25000000000000000000 5000037754294267 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037754294267/5000000000000000 : ℝ)) (X := (25000824595242803031/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100065931650843908841/100000000000000000000 : ℝ) ≤ (5000754492016129/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (100065931650843908841/100000000000000000000 : ℝ)^1024 ≤ (5000754492016129/5000000000000000 : ℝ)^4473 := by
      have hnat : (100065931650843908841 : ℕ)^1024*5000000000000000^4473 ≤ 5000754492016129^4473*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065931650843908841 100000000000000000000 5000754492016129 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000754492016129/5000000000000000 : ℝ)) (X := (100065931650843908841/100000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064282460358302779/50000000000000000000 : ℝ) ≤ (5001471229737991/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (50064282460358302779/50000000000000000000 : ℝ)^1024 ≤ (5001471229737991/5000000000000000 : ℝ)^4473 := by
      have hnat : (50064282460358302779 : ℕ)^1024*5000000000000000^4473 ≤ 5001471229737991^4473*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064282460358302779 50000000000000000000 5001471229737991 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001471229737991/5000000000000000 : ℝ)) (X := (50064282460358302779/50000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(824595242803031/50000000000000000000 : ℝ) ≤ ((52753877578926189863/52765000000000000000 : ℝ)+2*(358368860931/263825000000000 : ℝ)*(8037/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (52753877578926189863/52765000000000000000 : ℝ)+2*(358368860931/263825000000000 : ℝ)*(8037/100000 : ℝ)=(5000037754294267/5000000000000000 : ℝ) by norm_num, show 1+2*(824595242803031/50000000000000000000 : ℝ)=(25000824595242803031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64282460358302779/100000000000000000000 : ℝ)+(824595242803031/50000000000000000000 : ℝ) ≤ ((52753877578926189863/52765000000000000000 : ℝ)+(358368860931/263825000000000 : ℝ)*((1859/10000 : ℝ)+(8037/100000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (52753877578926189863/52765000000000000000 : ℝ)+(358368860931/263825000000000 : ℝ)*((1859/10000 : ℝ)+(8037/100000 : ℝ))=(5000754492016129/5000000000000000 : ℝ) by norm_num, show 1+(64282460358302779/100000000000000000000 : ℝ)+(824595242803031/50000000000000000000 : ℝ)=(100065931650843908841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64282460358302779/100000000000000000000 : ℝ) ≤ ((52753877578926189863/52765000000000000000 : ℝ)+2*(358368860931/263825000000000 : ℝ)*(1859/10000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (52753877578926189863/52765000000000000000 : ℝ)+2*(358368860931/263825000000000 : ℝ)*(1859/10000 : ℝ)=(5001471229737991/5000000000000000 : ℝ) by norm_num, show 1+2*(64282460358302779/100000000000000000000 : ℝ)=(50064282460358302779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52753877578926189863/52765000000000000000 : ℝ)*(X 1 0+X 2 0)+(358368860931/263825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (8037/100000 : ℝ)) (hi := (1859/10000 : ℝ)) (c := (52753877578926189863/52765000000000000000 : ℝ)) (alpha := (358368860931/263825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52753877578926189863/52765000000000000000 : ℝ)*(X 0 1+X 2 1)+(358368860931/263825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (8037/100000 : ℝ)) (hi := (1859/10000 : ℝ)) (c := (52753877578926189863/52765000000000000000 : ℝ)) (alpha := (358368860931/263825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52753877578926189863/52765000000000000000 : ℝ)*(X 0 2+X 1 2)+(358368860931/263825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (8037/100000 : ℝ)) (hi := (1859/10000 : ℝ)) (c := (52753877578926189863/52765000000000000000 : ℝ)) (alpha := (358368860931/263825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-948865247/5000000000 : ℝ)*X 0 0+(683207359/1250000000 : ℝ)*X 0 1+(5190127283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360446649/10000000000 : ℝ)*X 1 0+(-2039774477/10000000000 : ℝ)*X 1 1+(5190126951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360446729/10000000000 : ℝ)*X 2 0+(5190126649/10000000000 : ℝ)*X 2 1+(-127485923/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85550033/200000000 : ℝ)*X 0 0+(795941431/2000000000 : ℝ)*X 0 1+(459438657/1000000000 : ℝ)*X 0 2+(85550033/200000000 : ℝ)*X 1 0+(795941431/2000000000 : ℝ)*X 1 1+(459438657/1000000000 : ℝ)*X 1 2+(85550033/200000000 : ℝ)*X 2 0+(795941431/2000000000 : ℝ)*X 2 1+(459438657/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1897787703/10000000000 : ℝ)*X 0 0+(5191895453/10000000000 : ℝ)*X 0 1+(2731937831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288350807/10000000000 : ℝ)*X 1 0+(-1766025721/10000000000 : ℝ)*X 1 1+(2731938779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288352527/10000000000 : ℝ)*X 2 0+(5463874807/10000000000 : ℝ)*X 2 1+(-883013593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138817743/5000000000 : ℝ)*X 0 0+(1147611927/2500000000 : ℝ)*X 0 1+(3983679667/10000000000 : ℝ)*X 0 2+(2138817743/5000000000 : ℝ)*X 1 0+(1147611927/2500000000 : ℝ)*X 1 1+(3983679667/10000000000 : ℝ)*X 1 2+(2138817743/5000000000 : ℝ)*X 2 0+(1147611927/2500000000 : ℝ)*X 2 1+(3983679667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345033883516398512748928821/65956250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1918238827/100000000000000 : ℝ)*(base19) + (457359081/25000000000000 : ℝ)*(base23) + (11455371/100000000000000 : ℝ)*(upper2) + (160792523/50000000000000 : ℝ)*(upper3) + (2752893/3125000000000 : ℝ)*(upper4) + (131406834607439/5000000000000 : ℝ)*(major0) + (131406834607439/5000000000000 : ℝ)*(major1) + (131406834607439/5000000000000 : ℝ)*(major2) + (3629371394087361/100000000000000 : ℝ)*(sp0) + (1814693515469673/50000000000000 : ℝ)*(sp1) + (72587742394837/2000000000000 : ℝ)*(sp2) + (1626872598982919/100000000000000 : ℝ)*(sp3) + (17555090813/100000000000000 : ℝ)*(sp4) + (11661761333/100000000000000 : ℝ)*(sp7) + (406721065186063/25000000000000 : ℝ)*(f.failure) + (1814694474589087/50000000000000 : ℝ)*(f.sum) + (95568915467149/10553000000000000000000000000 : ℝ)*base65 + (2619506365031259143/263825000000000000000000000000000 : ℝ)*base68 + (2773455381082759143/263825000000000000000000000000000 : ℝ)*base70 + (152552780280159143/263825000000000000000000000000000 : ℝ)*base72 + (10557452624993/10553000000000000000000000000 : ℝ)*base73 + (930950839057715857/263825000000000000000000000000000 : ℝ)*base75 + (1357957886132359143/263825000000000000000000000000000 : ℝ)*base78 + (4644645682897684143/263825000000000000000000000000000 : ℝ)*base80 + (25181958594371/10553000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8088773/2500000000000000000000 : ℝ)*base89 + (8088773/2500000000000000000000 : ℝ)*base91 + (8088773/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144115879754720149571001/26382500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22207073/50000000000000 : ℝ)*(base8) + (674222941/100000000000000 : ℝ)*(lower2) + (260732111/100000000000000 : ℝ)*(upper3) + (106556403/50000000000000 : ℝ)*(lower4) + (2662436286985321/100000000000000 : ℝ)*(major0) + (2662436286985321/100000000000000 : ℝ)*(major1) + (2662436286985321/100000000000000 : ℝ)*(major2) + (6931674979/100000000000000 : ℝ)*(sp0) + (2969863757/12500000000000 : ℝ)*(sp1) + (3397857067/20000000000000 : ℝ)*(sp3) + (1838374411487907/50000000000000 : ℝ)*(sp4) + (3676732040154883/100000000000000 : ℝ)*(sp5) + (183837789953247/5000000000000 : ℝ)*(sp6) + (412024900883791/25000000000000 : ℝ)*(sp7) + (1648116592820499/100000000000000 : ℝ)*(f.failure) + (183837789953247/5000000000000 : ℝ)*(f.sum) + (528537833849943/26382500000000000000000000000 : ℝ)*base66 + (818185328715298977/5276500000000000000000000000000000 : ℝ)*base68 + (19239169414190701023/5276500000000000000000000000000000 : ℝ)*base69 + (10912202792616701023/5276500000000000000000000000000000 : ℝ)*base71 + (27541601247663/26382500000000000000000000000 : ℝ)*base74 + (39433685460748201023/5276500000000000000000000000000000 : ℝ)*base75 + (11198761798190798977/5276500000000000000000000000000000 : ℝ)*base78 + (13458722538690298977/5276500000000000000000000000000000 : ℝ)*base80 + (46310592884217/26382500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (37238671/10000000000000000000000 : ℝ)*base90 + (37238671/10000000000000000000000 : ℝ)*base92 + (37238671/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1859/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1489_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1489_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1489_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1489_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
