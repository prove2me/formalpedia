-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:58.519662+00:00
-- url     : https://prove2.me/submissions/0a89a338-82ac-41b2-83ef-48a5dbe6fc96

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
theorem support_rectangle_w1268_s0_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-3618289/19531250 : ℝ)*x 0 + (5884438/9765625 : ℝ)*x 1 + (18735149/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3618289/19531250 : ℝ)^8461 ≤ (10812736598451/100000000000000 : ℝ)^6413 := by
    have hnat : (3618289 : ℕ)^8461*100000000000000^6413 ≤ 10812736598451^6413*19531250^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3618289 19531250 10812736598451 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5884438/9765625 : ℝ)^8461 ≤ (51256534320169/100000000000000 : ℝ)^6413 := by
    have hnat : (5884438 : ℕ)^8461*100000000000000^6413 ≤ 51256534320169^6413*9765625^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5884438 9765625 51256534320169 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18735149/39062500 : ℝ)^8461 ≤ (37930729073451/100000000000000 : ℝ)^6413 := by
    have hnat : (18735149 : ℕ)^8461*100000000000000^6413 ≤ 37930729073451^6413*39062500^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18735149 39062500 37930729073451 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3618289/19531250 : ℝ), (5884438/9765625 : ℝ), (18735149/39062500 : ℝ)] ![(10812736598451/100000000000000 : ℝ), (51256534320169/100000000000000 : ℝ), (37930729073451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3618289/19531250 : ℝ)|^8461 ≤ (10812736598451/100000000000000 : ℝ)^6413
        have hw : |(-3618289/19531250 : ℝ)|=(3618289/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5884438/9765625 : ℝ)|^8461 ≤ (51256534320169/100000000000000 : ℝ)^6413
        have hw : |(5884438/9765625 : ℝ)|=(5884438/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18735149/39062500 : ℝ)|^8461 ≤ (37930729073451/100000000000000 : ℝ)^6413
        have hw : |(18735149/39062500 : ℝ)|=(18735149/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5509694761/10000000000 : ℝ)*x 0 + (-638681983/2500000000 : ℝ)*x 1 + (2398099059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509694761/10000000000 : ℝ)^8461 ≤ (45546633049271/100000000000000 : ℝ)^6413 := by
    have hnat : (5509694761 : ℕ)^8461*100000000000000^6413 ≤ 45546633049271^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509694761 10000000000 45546633049271 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (638681983/2500000000 : ℝ)^8461 ≤ (8261319068531/50000000000000 : ℝ)^6413 := by
    have hnat : (638681983 : ℕ)^8461*50000000000000^6413 ≤ 8261319068531^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638681983 2500000000 8261319068531 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398099059/5000000000 : ℝ)^8461 ≤ (7586145760433/20000000000000 : ℝ)^6413 := by
    have hnat : (2398099059 : ℕ)^8461*20000000000000^6413 ≤ 7586145760433^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398099059 5000000000 7586145760433 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509694761/10000000000 : ℝ), (-638681983/2500000000 : ℝ), (2398099059/5000000000 : ℝ)] ![(45546633049271/100000000000000 : ℝ), (8261319068531/50000000000000 : ℝ), (7586145760433/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509694761/10000000000 : ℝ)|^8461 ≤ (45546633049271/100000000000000 : ℝ)^6413
        have hw : |(5509694761/10000000000 : ℝ)|=(5509694761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-638681983/2500000000 : ℝ)|^8461 ≤ (8261319068531/50000000000000 : ℝ)^6413
        have hw : |(-638681983/2500000000 : ℝ)|=(638681983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398099059/5000000000 : ℝ)|^8461 ≤ (7586145760433/20000000000000 : ℝ)^6413
        have hw : |(2398099059/5000000000 : ℝ)|=(2398099059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5509694787/10000000000 : ℝ)*x 0 + (2398099059/5000000000 : ℝ)*x 1 + (-1277363949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509694787/10000000000 : ℝ)^8461 ≤ (45546633332843/100000000000000 : ℝ)^6413 := by
    have hnat : (5509694787 : ℕ)^8461*100000000000000^6413 ≤ 45546633332843^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509694787 10000000000 45546633332843 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2398099059/5000000000 : ℝ)^8461 ≤ (7586145760433/20000000000000 : ℝ)^6413 := by
    have hnat : (2398099059 : ℕ)^8461*20000000000000^6413 ≤ 7586145760433^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398099059 5000000000 7586145760433 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277363949/5000000000 : ℝ)^8461 ≤ (3304527569389/20000000000000 : ℝ)^6413 := by
    have hnat : (1277363949 : ℕ)^8461*20000000000000^6413 ≤ 3304527569389^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277363949 5000000000 3304527569389 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509694787/10000000000 : ℝ), (2398099059/5000000000 : ℝ), (-1277363949/5000000000 : ℝ)] ![(45546633332843/100000000000000 : ℝ), (7586145760433/20000000000000 : ℝ), (3304527569389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509694787/10000000000 : ℝ)|^8461 ≤ (45546633332843/100000000000000 : ℝ)^6413
        have hw : |(5509694787/10000000000 : ℝ)|=(5509694787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2398099059/5000000000 : ℝ)|^8461 ≤ (7586145760433/20000000000000 : ℝ)^6413
        have hw : |(2398099059/5000000000 : ℝ)|=(2398099059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1277363949/5000000000 : ℝ)|^8461 ≤ (3304527569389/20000000000000 : ℝ)^6413
        have hw : |(-1277363949/5000000000 : ℝ)|=(1277363949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4190987061/10000000000 : ℝ)*x 0 + (194746513/625000000 : ℝ)*x 1 + (224901209/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190987061/10000000000 : ℝ)^8461 ≤ (31746988828871/100000000000000 : ℝ)^6413 := by
    have hnat : (4190987061 : ℕ)^8461*100000000000000^6413 ≤ 31746988828871^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190987061 10000000000 31746988828871 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194746513/625000000 : ℝ)^8461 ≤ (5367930401809/25000000000000 : ℝ)^6413 := by
    have hnat : (194746513 : ℕ)^8461*25000000000000^6413 ≤ 5367930401809^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194746513 625000000 5367930401809 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224901209/400000000 : ℝ)^8461 ≤ (23390644774639/50000000000000 : ℝ)^6413 := by
    have hnat : (224901209 : ℕ)^8461*50000000000000^6413 ≤ 23390644774639^6413*400000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224901209 400000000 23390644774639 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190987061/10000000000 : ℝ), (194746513/625000000 : ℝ), (224901209/400000000 : ℝ)] ![(31746988828871/100000000000000 : ℝ), (5367930401809/25000000000000 : ℝ), (23390644774639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190987061/10000000000 : ℝ)|^8461 ≤ (31746988828871/100000000000000 : ℝ)^6413
        have hw : |(4190987061/10000000000 : ℝ)|=(4190987061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194746513/625000000 : ℝ)|^8461 ≤ (5367930401809/25000000000000 : ℝ)^6413
        have hw : |(194746513/625000000 : ℝ)|=(194746513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224901209/400000000 : ℝ)|^8461 ≤ (23390644774639/50000000000000 : ℝ)^6413
        have hw : |(224901209/400000000 : ℝ)|=(224901209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-464336991/2500000000 : ℝ)*x 0 + (4827842097/10000000000 : ℝ)*x 1 + (1198580269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464336991/2500000000 : ℝ)^8461 ≤ (5424795637727/50000000000000 : ℝ)^6413 := by
    have hnat : (464336991 : ℕ)^8461*50000000000000^6413 ≤ 5424795637727^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464336991 2500000000 5424795637727 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827842097/10000000000 : ℝ)^8461 ≤ (19130626104271/50000000000000 : ℝ)^6413 := by
    have hnat : (4827842097 : ℕ)^8461*50000000000000^6413 ≤ 19130626104271^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827842097 10000000000 19130626104271 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198580269/2000000000 : ℝ)^8461 ≤ (50889156497267/100000000000000 : ℝ)^6413 := by
    have hnat : (1198580269 : ℕ)^8461*100000000000000^6413 ≤ 50889156497267^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198580269 2000000000 50889156497267 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464336991/2500000000 : ℝ), (4827842097/10000000000 : ℝ), (1198580269/2000000000 : ℝ)] ![(5424795637727/50000000000000 : ℝ), (19130626104271/50000000000000 : ℝ), (50889156497267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464336991/2500000000 : ℝ)|^8461 ≤ (5424795637727/50000000000000 : ℝ)^6413
        have hw : |(-464336991/2500000000 : ℝ)|=(464336991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827842097/10000000000 : ℝ)|^8461 ≤ (19130626104271/50000000000000 : ℝ)^6413
        have hw : |(4827842097/10000000000 : ℝ)|=(4827842097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198580269/2000000000 : ℝ)|^8461 ≤ (50889156497267/100000000000000 : ℝ)^6413
        have hw : |(1198580269/2000000000 : ℝ)|=(1198580269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5175067241/10000000000 : ℝ)*x 0 + (-1358022261/10000000000 : ℝ)*x 1 + (5992903807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175067241/10000000000 : ℝ)^8461 ≤ (41932880240161/100000000000000 : ℝ)^6413 := by
    have hnat : (5175067241 : ℕ)^8461*100000000000000^6413 ≤ 41932880240161^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175067241 10000000000 41932880240161 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358022261/10000000000 : ℝ)^8461 ≤ (1435587133251/20000000000000 : ℝ)^6413 := by
    have hnat : (1358022261 : ℕ)^8461*20000000000000^6413 ≤ 1435587133251^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358022261 10000000000 1435587133251 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5992903807/10000000000 : ℝ)^8461 ≤ (50889184079959/100000000000000 : ℝ)^6413 := by
    have hnat : (5992903807 : ℕ)^8461*100000000000000^6413 ≤ 50889184079959^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992903807 10000000000 50889184079959 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175067241/10000000000 : ℝ), (-1358022261/10000000000 : ℝ), (5992903807/10000000000 : ℝ)] ![(41932880240161/100000000000000 : ℝ), (1435587133251/20000000000000 : ℝ), (50889184079959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175067241/10000000000 : ℝ)|^8461 ≤ (41932880240161/100000000000000 : ℝ)^6413
        have hw : |(5175067241/10000000000 : ℝ)|=(5175067241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358022261/10000000000 : ℝ)|^8461 ≤ (1435587133251/20000000000000 : ℝ)^6413
        have hw : |(-1358022261/10000000000 : ℝ)|=(1358022261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5992903807/10000000000 : ℝ)|^8461 ≤ (50889184079959/100000000000000 : ℝ)^6413
        have hw : |(5992903807/10000000000 : ℝ)|=(5992903807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646883543/1250000000 : ℝ)*x 0 + (5992901759/10000000000 : ℝ)*x 1 + (-67901193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646883543/1250000000 : ℝ)^8461 ≤ (20966446015907/50000000000000 : ℝ)^6413 := by
    have hnat : (646883543 : ℕ)^8461*50000000000000^6413 ≤ 20966446015907^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646883543 1250000000 20966446015907 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5992901759/10000000000 : ℝ)^8461 ≤ (50889161135461/100000000000000 : ℝ)^6413 := by
    have hnat : (5992901759 : ℕ)^8461*100000000000000^6413 ≤ 50889161135461^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992901759 10000000000 50889161135461 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67901193/500000000 : ℝ)^8461 ≤ (7177946816943/100000000000000 : ℝ)^6413 := by
    have hnat : (67901193 : ℕ)^8461*100000000000000^6413 ≤ 7177946816943^6413*500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67901193 500000000 7177946816943 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646883543/1250000000 : ℝ), (5992901759/10000000000 : ℝ), (-67901193/500000000 : ℝ)] ![(20966446015907/50000000000000 : ℝ), (50889161135461/100000000000000 : ℝ), (7177946816943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646883543/1250000000 : ℝ)|^8461 ≤ (20966446015907/50000000000000 : ℝ)^6413
        have hw : |(646883543/1250000000 : ℝ)|=(646883543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5992901759/10000000000 : ℝ)|^8461 ≤ (50889161135461/100000000000000 : ℝ)^6413
        have hw : |(5992901759/10000000000 : ℝ)|=(5992901759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67901193/500000000 : ℝ)|^8461 ≤ (7177946816943/100000000000000 : ℝ)^6413
        have hw : |(-67901193/500000000 : ℝ)|=(67901193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s0_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2100371691/5000000000 : ℝ)*x 0 + (2779010951/5000000000 : ℝ)*x 1 + (159136711/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100371691/5000000000 : ℝ)^8461 ≤ (6368906274351/20000000000000 : ℝ)^6413 := by
    have hnat : (2100371691 : ℕ)^8461*20000000000000^6413 ≤ 6368906274351^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100371691 5000000000 6368906274351 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779010951/5000000000 : ℝ)^8461 ≤ (4607445436321/10000000000000 : ℝ)^6413 := by
    have hnat : (2779010951 : ℕ)^8461*10000000000000^6413 ≤ 4607445436321^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779010951 5000000000 4607445436321 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159136711/500000000 : ℝ)^8461 ≤ (2208101423699/10000000000000 : ℝ)^6413 := by
    have hnat : (159136711 : ℕ)^8461*10000000000000^6413 ≤ 2208101423699^6413*500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159136711 500000000 2208101423699 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100371691/5000000000 : ℝ), (2779010951/5000000000 : ℝ), (159136711/500000000 : ℝ)] ![(6368906274351/20000000000000 : ℝ), (4607445436321/10000000000000 : ℝ), (2208101423699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100371691/5000000000 : ℝ)|^8461 ≤ (6368906274351/20000000000000 : ℝ)^6413
        have hw : |(2100371691/5000000000 : ℝ)|=(2100371691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779010951/5000000000 : ℝ)|^8461 ≤ (4607445436321/10000000000000 : ℝ)^6413
        have hw : |(2779010951/5000000000 : ℝ)|=(2779010951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159136711/500000000 : ℝ)|^8461 ≤ (2208101423699/10000000000000 : ℝ)^6413
        have hw : |(159136711/500000000 : ℝ)|=(159136711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (921/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27339/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2115/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2115 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2115*1^512 ≤ 0^512*1^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2115/512 : ℝ) ≤ (1135365749683340757/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2115 ≤ (1135365749683340757/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2115*50000000000000000000^512 ≤ 1135365749683340757^512*5^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1135365749683340757 50000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1135365749683340757/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2115 := by
      have hnat : (1 : ℕ)^512*1^2115 ≤ 1^2115*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51135365749683340757/50000000000000000000 : ℝ) ≤ (1256812890739559/1250000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (51135365749683340757/50000000000000000000 : ℝ)^512 ≤ (1256812890739559/1250000000000000 : ℝ)^2115 := by
      have hnat : (51135365749683340757 : ℕ)^512*1250000000000000^2115 ≤ 1256812890739559^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51135365749683340757 50000000000000000000 1256812890739559 1250000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256812890739559/1250000000000000 : ℝ)) (X := (51135365749683340757/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26135365749683340757/25000000000000000000 : ℝ) ≤ (631812890739559/625000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (26135365749683340757/25000000000000000000 : ℝ)^512 ≤ (631812890739559/625000000000000 : ℝ)^2115 := by
      have hnat : (26135365749683340757 : ℕ)^512*625000000000000^2115 ≤ 631812890739559^2115*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26135365749683340757 25000000000000000000 631812890739559 625000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631812890739559/625000000000000 : ℝ)) (X := (26135365749683340757/25000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6812890739559/500000000000000 : ℝ)*(0 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(6812890739559/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1135365749683340757/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6812890739559/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (1 : ℝ)+(6812890739559/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256812890739559/1250000000000000 : ℝ) by norm_num, show 1+(1135365749683340757/50000000000000000000 : ℝ)+(0 : ℝ)=(51135365749683340757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1135365749683340757/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6812890739559/500000000000000 : ℝ)*(2/5 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(6812890739559/500000000000000 : ℝ)*(2/5 : ℝ)=(631812890739559/625000000000000 : ℝ) by norm_num, show 1+2*(1135365749683340757/50000000000000000000 : ℝ)=(26135365749683340757/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6812890739559/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6812890739559/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6812890739559/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6812890739559/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6812890739559/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6812890739559/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3618289/19531250 : ℝ)*X 0 0+(5884438/9765625 : ℝ)*X 0 1+(18735149/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5509694761/10000000000 : ℝ)*X 1 0+(-638681983/2500000000 : ℝ)*X 1 1+(2398099059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5509694787/10000000000 : ℝ)*X 2 0+(2398099059/5000000000 : ℝ)*X 2 1+(-1277363949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4190987061/10000000000 : ℝ)*X 0 0+(194746513/625000000 : ℝ)*X 0 1+(224901209/400000000 : ℝ)*X 0 2+(4190987061/10000000000 : ℝ)*X 1 0+(194746513/625000000 : ℝ)*X 1 1+(224901209/400000000 : ℝ)*X 1 2+(4190987061/10000000000 : ℝ)*X 2 0+(194746513/625000000 : ℝ)*X 2 1+(224901209/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464336991/2500000000 : ℝ)*X 0 0+(4827842097/10000000000 : ℝ)*X 0 1+(1198580269/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175067241/10000000000 : ℝ)*X 1 0+(-1358022261/10000000000 : ℝ)*X 1 1+(5992903807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646883543/1250000000 : ℝ)*X 2 0+(5992901759/10000000000 : ℝ)*X 2 1+(-67901193/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100371691/5000000000 : ℝ)*X 0 0+(2779010951/5000000000 : ℝ)*X 0 1+(159136711/500000000 : ℝ)*X 0 2+(2100371691/5000000000 : ℝ)*X 1 0+(2779010951/5000000000 : ℝ)*X 1 1+(159136711/500000000 : ℝ)*X 1 2+(2100371691/5000000000 : ℝ)*X 2 0+(2779010951/5000000000 : ℝ)*X 2 1+(159136711/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122212221072872012960457/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56609521/100000000000000 : ℝ)*(base1) + (595590363/50000000000000 : ℝ)*(base19) + (1195018969/100000000000000 : ℝ)*(base23) + (134119327/100000000000000 : ℝ)*(upper3) + (71845797/50000000000000 : ℝ)*(upper5) + (606160565392047/100000000000000 : ℝ)*(major0) + (606160565392047/100000000000000 : ℝ)*(major1) + (606160565392047/100000000000000 : ℝ)*(major2) + (32534582299767/4000000000000 : ℝ)*(sp0) + (813367124197923/100000000000000 : ℝ)*(sp1) + (635443062781/78125000000 : ℝ)*(sp2) + (99737691149051/25000000000000 : ℝ)*(sp3) + (762898799/20000000000000 : ℝ)*(sp4) + (183125009/10000000000000 : ℝ)*(sp7) + (79790530491163/20000000000000 : ℝ)*(f.failure) + (813368315378649/100000000000000 : ℝ)*(f.sum) + (73577349212727/25000000000000000000000000000 : ℝ)*base66 + (58117470537273/50000000000000000000000000000 : ℝ)*base67 + (110312598137273/50000000000000000000000000000 : ℝ)*base69 + (19748504462727/50000000000000000000000000000 : ℝ)*base72 + (40022702512727/25000000000000000000000000000 : ℝ)*base74 + (89506123812727/50000000000000000000000000000 : ℝ)*base76 + (91211157687273/50000000000000000000000000000 : ℝ)*base77 + (188890385712727/50000000000000000000000000000 : ℝ)*base80 + (61358219612727/25000000000000000000000000000 : ℝ)*base82 + (349727/2000000000000000000000 : ℝ)*base90 + (349727/2000000000000000000000 : ℝ)*base92 + (349727/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53591385902449713768681/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252103351/100000000000000 : ℝ)*(base1) + (218201093/25000000000000 : ℝ)*(base19) + (255616043/25000000000000 : ℝ)*(base23) + (91291043/50000000000000 : ℝ)*(upper3) + (639663717208047/100000000000000 : ℝ)*(major0) + (639663717208047/100000000000000 : ℝ)*(major1) + (639663717208047/100000000000000 : ℝ)*(major2) + (237522229/12500000000000 : ℝ)*(sp1) + (692744089/50000000000000 : ℝ)*(sp2) + (376789571/100000000000000 : ℝ)*(sp3) + (214581086349331/25000000000000 : ℝ)*(sp4) + (858321320311769/100000000000000 : ℝ)*(sp5) + (429160842670811/50000000000000 : ℝ)*(sp6) + (421002569318831/100000000000000 : ℝ)*(sp7) + (210501599105877/50000000000000 : ℝ)*(f.failure) + (214581023323493/25000000000000 : ℝ)*(f.sum) + (94122522606273/25000000000000000000000000000 : ℝ)*base65 + (25121491868727/50000000000000000000000000000 : ℝ)*base68 + (133908557718727/50000000000000000000000000000 : ℝ)*base70 + (7107741668727/50000000000000000000000000000 : ℝ)*base72 + (81075541106273/25000000000000000000000000000 : ℝ)*base73 + (184494756668727/50000000000000000000000000000 : ℝ)*base76 + (42035029681273/50000000000000000000000000000 : ℝ)*base77 + (283067824431273/50000000000000000000000000000 : ℝ)*base79 + (57523257756273/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (15555567/5000000000000000000000 : ℝ)*base89 + (15555567/5000000000000000000000 : ℝ)*base91 + (15555567/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1268_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s1_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048083767/10000000000 : ℝ)*x 0 + (1133826613/2000000000 : ℝ)*x 1 + (5027573187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048083767/10000000000 : ℝ)^8461 ≤ (2468628261333/20000000000000 : ℝ)^6413 := by
    have hnat : (2048083767 : ℕ)^8461*20000000000000^6413 ≤ 2468628261333^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048083767 10000000000 2468628261333 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133826613/2000000000 : ℝ)^8461 ≤ (47293544961973/100000000000000 : ℝ)^6413 := by
    have hnat : (1133826613 : ℕ)^8461*100000000000000^6413 ≤ 47293544961973^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133826613 2000000000 47293544961973 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027573187/10000000000 : ℝ)^8461 ≤ (40363313713859/100000000000000 : ℝ)^6413 := by
    have hnat : (5027573187 : ℕ)^8461*100000000000000^6413 ≤ 40363313713859^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027573187 10000000000 40363313713859 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048083767/10000000000 : ℝ), (1133826613/2000000000 : ℝ), (5027573187/10000000000 : ℝ)] ![(2468628261333/20000000000000 : ℝ), (47293544961973/100000000000000 : ℝ), (40363313713859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048083767/10000000000 : ℝ)|^8461 ≤ (2468628261333/20000000000000 : ℝ)^6413
        have hw : |(-2048083767/10000000000 : ℝ)|=(2048083767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133826613/2000000000 : ℝ)|^8461 ≤ (47293544961973/100000000000000 : ℝ)^6413
        have hw : |(1133826613/2000000000 : ℝ)|=(1133826613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027573187/10000000000 : ℝ)|^8461 ≤ (40363313713859/100000000000000 : ℝ)^6413
        have hw : |(5027573187/10000000000 : ℝ)|=(5027573187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5412248303/10000000000 : ℝ)*x 0 + (-1196084479/5000000000 : ℝ)*x 1 + (5027573471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412248303/10000000000 : ℝ)^8461 ≤ (22243418786991/50000000000000 : ℝ)^6413 := by
    have hnat : (5412248303 : ℕ)^8461*50000000000000^6413 ≤ 22243418786991^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412248303 10000000000 22243418786991 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1196084479/5000000000 : ℝ)^8461 ≤ (3787461422981/25000000000000 : ℝ)^6413 := by
    have hnat : (1196084479 : ℕ)^8461*25000000000000^6413 ≤ 3787461422981^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196084479 5000000000 3787461422981 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027573471/10000000000 : ℝ)^8461 ≤ (20181658361031/50000000000000 : ℝ)^6413 := by
    have hnat : (5027573471 : ℕ)^8461*50000000000000^6413 ≤ 20181658361031^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027573471 10000000000 20181658361031 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412248303/10000000000 : ℝ), (-1196084479/5000000000 : ℝ), (5027573471/10000000000 : ℝ)] ![(22243418786991/50000000000000 : ℝ), (3787461422981/25000000000000 : ℝ), (20181658361031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412248303/10000000000 : ℝ)|^8461 ≤ (22243418786991/50000000000000 : ℝ)^6413
        have hw : |(5412248303/10000000000 : ℝ)|=(5412248303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1196084479/5000000000 : ℝ)|^8461 ≤ (3787461422981/25000000000000 : ℝ)^6413
        have hw : |(-1196084479/5000000000 : ℝ)|=(1196084479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027573471/10000000000 : ℝ)|^8461 ≤ (20181658361031/50000000000000 : ℝ)^6413
        have hw : |(5027573471/10000000000 : ℝ)|=(5027573471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706124281/5000000000 : ℝ)*x 0 + (5027573311/10000000000 : ℝ)*x 1 + (-299021103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706124281/5000000000 : ℝ)^8461 ≤ (44486840382739/100000000000000 : ℝ)^6413 := by
    have hnat : (2706124281 : ℕ)^8461*100000000000000^6413 ≤ 44486840382739^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706124281 5000000000 44486840382739 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027573311/10000000000 : ℝ)^8461 ≤ (403633150273/1000000000000 : ℝ)^6413 := by
    have hnat : (5027573311 : ℕ)^8461*1000000000000^6413 ≤ 403633150273^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027573311 10000000000 403633150273 1000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299021103/1250000000 : ℝ)^8461 ≤ (3787461143069/25000000000000 : ℝ)^6413 := by
    have hnat : (299021103 : ℕ)^8461*25000000000000^6413 ≤ 3787461143069^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299021103 1250000000 3787461143069 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706124281/5000000000 : ℝ), (5027573311/10000000000 : ℝ), (-299021103/1250000000 : ℝ)] ![(44486840382739/100000000000000 : ℝ), (403633150273/1000000000000 : ℝ), (3787461143069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706124281/5000000000 : ℝ)|^8461 ≤ (44486840382739/100000000000000 : ℝ)^6413
        have hw : |(2706124281/5000000000 : ℝ)|=(2706124281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027573311/10000000000 : ℝ)|^8461 ≤ (403633150273/1000000000000 : ℝ)^6413
        have hw : |(5027573311/10000000000 : ℝ)|=(5027573311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299021103/1250000000 : ℝ)|^8461 ≤ (3787461143069/25000000000000 : ℝ)^6413
        have hw : |(-299021103/1250000000 : ℝ)|=(299021103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (269161973/625000000 : ℝ)*x 0 + (925028003/2500000000 : ℝ)*x 1 + (5008098913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269161973/625000000 : ℝ)^8461 ≤ (6581483424697/20000000000000 : ℝ)^6413 := by
    have hnat : (269161973 : ℕ)^8461*20000000000000^6413 ≤ 6581483424697^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269161973 625000000 6581483424697 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925028003/2500000000 : ℝ)^8461 ≤ (26935418135509/100000000000000 : ℝ)^6413 := by
    have hnat : (925028003 : ℕ)^8461*100000000000000^6413 ≤ 26935418135509^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925028003 2500000000 26935418135509 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5008098913/10000000000 : ℝ)^8461 ≤ (20078582361951/50000000000000 : ℝ)^6413 := by
    have hnat : (5008098913 : ℕ)^8461*50000000000000^6413 ≤ 20078582361951^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008098913 10000000000 20078582361951 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269161973/625000000 : ℝ), (925028003/2500000000 : ℝ), (5008098913/10000000000 : ℝ)] ![(6581483424697/20000000000000 : ℝ), (26935418135509/100000000000000 : ℝ), (20078582361951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269161973/625000000 : ℝ)|^8461 ≤ (6581483424697/20000000000000 : ℝ)^6413
        have hw : |(269161973/625000000 : ℝ)|=(269161973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925028003/2500000000 : ℝ)|^8461 ≤ (26935418135509/100000000000000 : ℝ)^6413
        have hw : |(925028003/2500000000 : ℝ)|=(925028003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5008098913/10000000000 : ℝ)|^8461 ≤ (20078582361951/50000000000000 : ℝ)^6413
        have hw : |(5008098913/10000000000 : ℝ)|=(5008098913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024364917/5000000000 : ℝ)*x 0 + (5035915073/10000000000 : ℝ)*x 1 + (5660634143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024364917/5000000000 : ℝ)^8461 ≤ (6174139320749/50000000000000 : ℝ)^6413 := by
    have hnat : (1024364917 : ℕ)^8461*50000000000000^6413 ≤ 6174139320749^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024364917 5000000000 6174139320749 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035915073/10000000000 : ℝ)^8461 ≤ (2528231036749/6250000000000 : ℝ)^6413 := by
    have hnat : (5035915073 : ℕ)^8461*6250000000000^6413 ≤ 2528231036749^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035915073 10000000000 2528231036749 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660634143/10000000000 : ℝ)^8461 ≤ (47200024744629/100000000000000 : ℝ)^6413 := by
    have hnat : (5660634143 : ℕ)^8461*100000000000000^6413 ≤ 47200024744629^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660634143 10000000000 47200024744629 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024364917/5000000000 : ℝ), (5035915073/10000000000 : ℝ), (5660634143/10000000000 : ℝ)] ![(6174139320749/50000000000000 : ℝ), (2528231036749/6250000000000 : ℝ), (47200024744629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024364917/5000000000 : ℝ)|^8461 ≤ (6174139320749/50000000000000 : ℝ)^6413
        have hw : |(-1024364917/5000000000 : ℝ)|=(1024364917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035915073/10000000000 : ℝ)|^8461 ≤ (2528231036749/6250000000000 : ℝ)^6413
        have hw : |(5035915073/10000000000 : ℝ)|=(5035915073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660634143/10000000000 : ℝ)|^8461 ≤ (47200024744629/100000000000000 : ℝ)^6413
        have hw : |(5660634143/10000000000 : ℝ)|=(5660634143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246762781/10000000000 : ℝ)*x 0 + (-109944239/625000000 : ℝ)*x 1 + (5660634667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246762781/10000000000 : ℝ)^8461 ≤ (21350516822899/50000000000000 : ℝ)^6413 := by
    have hnat : (5246762781 : ℕ)^8461*50000000000000^6413 ≤ 21350516822899^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246762781 10000000000 21350516822899 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109944239/625000000 : ℝ)^8461 ≤ (2524733959401/25000000000000 : ℝ)^6413 := by
    have hnat : (109944239 : ℕ)^8461*25000000000000^6413 ≤ 2524733959401^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109944239 625000000 2524733959401 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660634667/10000000000 : ℝ)^8461 ≤ (1888001220369/4000000000000 : ℝ)^6413 := by
    have hnat : (5660634667 : ℕ)^8461*4000000000000^6413 ≤ 1888001220369^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660634667 10000000000 1888001220369 4000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246762781/10000000000 : ℝ), (-109944239/625000000 : ℝ), (5660634667/10000000000 : ℝ)] ![(21350516822899/50000000000000 : ℝ), (2524733959401/25000000000000 : ℝ), (1888001220369/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246762781/10000000000 : ℝ)|^8461 ≤ (21350516822899/50000000000000 : ℝ)^6413
        have hw : |(5246762781/10000000000 : ℝ)|=(5246762781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109944239/625000000 : ℝ)|^8461 ≤ (2524733959401/25000000000000 : ℝ)^6413
        have hw : |(-109944239/625000000 : ℝ)|=(109944239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660634667/10000000000 : ℝ)|^8461 ≤ (1888001220369/4000000000000 : ℝ)^6413
        have hw : |(5660634667/10000000000 : ℝ)|=(5660634667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (655845337/1250000000 : ℝ)*x 0 + (1415158587/2500000000 : ℝ)*x 1 + (-1759108407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655845337/1250000000 : ℝ)^8461 ≤ (21350516366551/50000000000000 : ℝ)^6413 := by
    have hnat : (655845337 : ℕ)^8461*50000000000000^6413 ≤ 21350516366551^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655845337 1250000000 21350516366551 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415158587/2500000000 : ℝ)^8461 ≤ (23600013499931/50000000000000 : ℝ)^6413 := by
    have hnat : (1415158587 : ℕ)^8461*50000000000000^6413 ≤ 23600013499931^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415158587 2500000000 23600013499931 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759108407/10000000000 : ℝ)^8461 ≤ (1262367531679/12500000000000 : ℝ)^6413 := by
    have hnat : (1759108407 : ℕ)^8461*12500000000000^6413 ≤ 1262367531679^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759108407 10000000000 1262367531679 12500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655845337/1250000000 : ℝ), (1415158587/2500000000 : ℝ), (-1759108407/10000000000 : ℝ)] ![(21350516366551/50000000000000 : ℝ), (23600013499931/50000000000000 : ℝ), (1262367531679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655845337/1250000000 : ℝ)|^8461 ≤ (21350516366551/50000000000000 : ℝ)^6413
        have hw : |(655845337/1250000000 : ℝ)|=(655845337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415158587/2500000000 : ℝ)|^8461 ≤ (23600013499931/50000000000000 : ℝ)^6413
        have hw : |(1415158587/2500000000 : ℝ)|=(1415158587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759108407/10000000000 : ℝ)|^8461 ≤ (1262367531679/12500000000000 : ℝ)^6413
        have hw : |(-1759108407/10000000000 : ℝ)|=(1759108407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s1_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4307908371/10000000000 : ℝ)*x 0 + (4991092039/10000000000 : ℝ)*x 1 + (1858719783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307908371/10000000000 : ℝ)^8461 ≤ (2057543311297/6250000000000 : ℝ)^6413 := by
    have hnat : (4307908371 : ℕ)^8461*6250000000000^6413 ≤ 2057543311297^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307908371 10000000000 2057543311297 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991092039/10000000000 : ℝ)^8461 ≤ (19988672079709/50000000000000 : ℝ)^6413 := by
    have hnat : (4991092039 : ℕ)^8461*50000000000000^6413 ≤ 19988672079709^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991092039 10000000000 19988672079709 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858719783/5000000000 : ℝ)^8461 ≤ (13550981423803/50000000000000 : ℝ)^6413 := by
    have hnat : (1858719783 : ℕ)^8461*50000000000000^6413 ≤ 13550981423803^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858719783 5000000000 13550981423803 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307908371/10000000000 : ℝ), (4991092039/10000000000 : ℝ), (1858719783/5000000000 : ℝ)] ![(2057543311297/6250000000000 : ℝ), (19988672079709/50000000000000 : ℝ), (13550981423803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307908371/10000000000 : ℝ)|^8461 ≤ (2057543311297/6250000000000 : ℝ)^6413
        have hw : |(4307908371/10000000000 : ℝ)|=(4307908371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991092039/10000000000 : ℝ)|^8461 ≤ (19988672079709/50000000000000 : ℝ)^6413
        have hw : |(4991092039/10000000000 : ℝ)|=(4991092039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858719783/5000000000 : ℝ)|^8461 ≤ (13550981423803/50000000000000 : ℝ)^6413
        have hw : |(1858719783/5000000000 : ℝ)|=(1858719783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3163/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1989/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (921/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (389621405201/100000000000000000000 : ℝ) := by
    have hpowers : (921/100000 : ℝ)^2115 ≤ (389621405201/100000000000000000000 : ℝ)^512 := by
      have hnat : (921 : ℕ)^2115*100000000000000000000^512 ≤ 389621405201^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 100000 389621405201 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/100000 : ℝ)) (X := (389621405201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27339/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (235720976004317311/50000000000000000000 : ℝ) := by
    have hpowers : (27339/100000 : ℝ)^2115 ≤ (235720976004317311/50000000000000000000 : ℝ)^512 := by
      have hnat : (27339 : ℕ)^2115*50000000000000000000^512 ≤ 235720976004317311^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27339 100000 235720976004317311 50000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27339/100000 : ℝ)) (X := (235720976004317311/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000389621405201/50000000000000000000 : ℝ) ≤ (500000000943197/500000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50000000389621405201/50000000000000000000 : ℝ)^512 ≤ (500000000943197/500000000000000 : ℝ)^2115 := by
      have hnat : (50000000389621405201 : ℕ)^512*500000000000000^2115 ≤ 500000000943197^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000389621405201 50000000000000000000 500000000943197 500000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000943197/500000000000000 : ℝ)) (X := (50000000389621405201/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100471442341630039823/100000000000000000000 : ℝ) ≤ (400455694421051/400000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (100471442341630039823/100000000000000000000 : ℝ)^512 ≤ (400455694421051/400000000000000 : ℝ)^2115 := by
      have hnat : (100471442341630039823 : ℕ)^512*400000000000000^2115 ≤ 400455694421051^2115*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100471442341630039823 100000000000000000000 400455694421051 400000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400455694421051/400000000000000 : ℝ)) (X := (100471442341630039823/100000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25235720976004317311/25000000000000000000 : ℝ) ≤ (1002278470218861/1000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (25235720976004317311/25000000000000000000 : ℝ)^512 ≤ (1002278470218861/1000000000000000 : ℝ)^2115 := by
      have hnat : (25235720976004317311 : ℕ)^512*1000000000000000^2115 ≤ 1002278470218861^2115*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25235720976004317311 25000000000000000000 1002278470218861 1000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002278470218861/1000000000000000 : ℝ)) (X := (25235720976004317311/25000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(389621405201/100000000000000000000 : ℝ) ≤ ((1761060105366703639/1761200000000000000 : ℝ)+2*(2278468332467/528360000000000 : ℝ)*(921/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1761060105366703639/1761200000000000000 : ℝ)+2*(2278468332467/528360000000000 : ℝ)*(921/100000 : ℝ)=(500000000943197/500000000000000 : ℝ) by norm_num, show 1+2*(389621405201/100000000000000000000 : ℝ)=(50000000389621405201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(235720976004317311/50000000000000000000 : ℝ)+(389621405201/100000000000000000000 : ℝ) ≤ ((1761060105366703639/1761200000000000000 : ℝ)+(2278468332467/528360000000000 : ℝ)*((27339/100000 : ℝ)+(921/100000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (1761060105366703639/1761200000000000000 : ℝ)+(2278468332467/528360000000000 : ℝ)*((27339/100000 : ℝ)+(921/100000 : ℝ))=(400455694421051/400000000000000 : ℝ) by norm_num, show 1+(235720976004317311/50000000000000000000 : ℝ)+(389621405201/100000000000000000000 : ℝ)=(100471442341630039823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(235720976004317311/50000000000000000000 : ℝ) ≤ ((1761060105366703639/1761200000000000000 : ℝ)+2*(2278468332467/528360000000000 : ℝ)*(27339/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (1761060105366703639/1761200000000000000 : ℝ)+2*(2278468332467/528360000000000 : ℝ)*(27339/100000 : ℝ)=(1002278470218861/1000000000000000 : ℝ) by norm_num, show 1+2*(235720976004317311/50000000000000000000 : ℝ)=(25235720976004317311/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1761060105366703639/1761200000000000000 : ℝ)*(X 1 0+X 2 0)+(2278468332467/528360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (921/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (1761060105366703639/1761200000000000000 : ℝ)) (alpha := (2278468332467/528360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1761060105366703639/1761200000000000000 : ℝ)*(X 0 1+X 2 1)+(2278468332467/528360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (921/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (1761060105366703639/1761200000000000000 : ℝ)) (alpha := (2278468332467/528360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1761060105366703639/1761200000000000000 : ℝ)*(X 0 2+X 1 2)+(2278468332467/528360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (921/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (1761060105366703639/1761200000000000000 : ℝ)) (alpha := (2278468332467/528360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2048083767/10000000000 : ℝ)*X 0 0+(1133826613/2000000000 : ℝ)*X 0 1+(5027573187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412248303/10000000000 : ℝ)*X 1 0+(-1196084479/5000000000 : ℝ)*X 1 1+(5027573471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706124281/5000000000 : ℝ)*X 2 0+(5027573311/10000000000 : ℝ)*X 2 1+(-299021103/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269161973/625000000 : ℝ)*X 0 0+(925028003/2500000000 : ℝ)*X 0 1+(5008098913/10000000000 : ℝ)*X 0 2+(269161973/625000000 : ℝ)*X 1 0+(925028003/2500000000 : ℝ)*X 1 1+(5008098913/10000000000 : ℝ)*X 1 2+(269161973/625000000 : ℝ)*X 2 0+(925028003/2500000000 : ℝ)*X 2 1+(5008098913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1024364917/5000000000 : ℝ)*X 0 0+(5035915073/10000000000 : ℝ)*X 0 1+(5660634143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246762781/10000000000 : ℝ)*X 1 0+(-109944239/625000000 : ℝ)*X 1 1+(5660634667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655845337/1250000000 : ℝ)*X 2 0+(1415158587/2500000000 : ℝ)*X 2 1+(-1759108407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307908371/10000000000 : ℝ)*X 0 0+(4991092039/10000000000 : ℝ)*X 0 1+(1858719783/5000000000 : ℝ)*X 0 2+(4307908371/10000000000 : ℝ)*X 1 0+(4991092039/10000000000 : ℝ)*X 1 1+(1858719783/5000000000 : ℝ)*X 1 2+(4307908371/10000000000 : ℝ)*X 2 0+(4991092039/10000000000 : ℝ)*X 2 1+(1858719783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1874793231497896513235917/343984375000000000000000000000 : ℝ) := by norm_num
    linear_combination (38772219/100000000000000 : ℝ)*(base1) + (49892863/4000000000000 : ℝ)*(base19) + (52876519/4000000000000 : ℝ)*(base23) + (123396451/100000000000000 : ℝ)*(upper3) + (48355371/25000000000000 : ℝ)*(upper5) + (36300907888117/3125000000000 : ℝ)*(major0) + (36300907888117/3125000000000 : ℝ)*(major1) + (36300907888117/3125000000000 : ℝ)*(major2) + (389677021121187/25000000000000 : ℝ)*(sp0) + (1558715037717031/100000000000000 : ℝ)*(sp1) + (1558714963125631/100000000000000 : ℝ)*(sp2) + (95567211650201/12500000000000 : ℝ)*(sp3) + (8239326077/100000000000000 : ℝ)*(sp4) + (390615279/10000000000000 : ℝ)*(sp7) + (764541638126617/100000000000000 : ℝ)*(f.failure) + (779358142519303/50000000000000 : ℝ)*(f.sum) + (860734049681/3302250000000000000000000000 : ℝ)*base65 + (2364946747765267/971250000000000000000000000000 : ℝ)*base67 + (4461517661194733/971250000000000000000000000000 : ℝ)*base70 + (654950659684733/971250000000000000000000000000 : ℝ)*base72 + (4396120106869/1651125000000000000000000000 : ℝ)*base73 + (2406399214082767/971250000000000000000000000000 : ℝ)*base75 + (1888613007899017/971250000000000000000000000000 : ℝ)*base77 + (1729377259015267/971250000000000000000000000000 : ℝ)*base79 + (10325749441369/3302250000000000000000000000 : ℝ)*base82 + (28074107/10000000000000000000000 : ℝ)*base89 + (28074107/10000000000000000000000 : ℝ)*base91 + (28074107/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (452192531652634884726527433/44030000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4408569/10000000000000 : ℝ)*(base1) + (2011081203/100000000000000 : ℝ)*(base19) + (30436923/1562500000000 : ℝ)*(base23) + (1086783/400000000000 : ℝ)*(upper3) + (225453709/100000000000000 : ℝ)*(upper5) + (1192931413827549/100000000000000 : ℝ)*(major0) + (1192931413827549/100000000000000 : ℝ)*(major1) + (1192931413827549/100000000000000 : ℝ)*(major2) + (10424082663/100000000000000 : ℝ)*(sp1) + (9245078561/100000000000000 : ℝ)*(sp2) + (400179706262879/25000000000000 : ℝ)*(sp4) + (40017658645049/2500000000000 : ℝ)*(sp5) + (1600707587924193/100000000000000 : ℝ)*(sp6) + (78514366026689/10000000000000 : ℝ)*(sp7) + (39257185217629/5000000000000 : ℝ)*(f.failure) + (800359390482913/50000000000000 : ℝ)*(f.sum) + (3662144430517/1761200000000000000000000000 : ℝ)*base65 + (380098745411717/10360000000000000000000000000000 : ℝ)*base68 + (56106447059411717/10360000000000000000000000000000 : ℝ)*base70 + (43977760001371717/10360000000000000000000000000000 : ℝ)*base72 + (7642155846513/1761200000000000000000000000 : ℝ)*base73 + (9474738239211717/10360000000000000000000000000000 : ℝ)*base76 + (52050913917331717/10360000000000000000000000000000 : ℝ)*base78 + (11306333836468283/10360000000000000000000000000000 : ℝ)*base79 + (1562562477089/8806000000000000000000000000 : ℝ)*base82 + (1309241/500000000000000000000 : ℝ)*base90 + (1309241/500000000000000000000 : ℝ)*base92 + (1309241/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1268_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3163/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1989/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s2_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047418267/5000000000 : ℝ)*x 0 + (5488431253/10000000000 : ℝ)*x 1 + (647304543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047418267/5000000000 : ℝ)^8461 ≤ (2543246980839/20000000000000 : ℝ)^6413 := by
    have hnat : (1047418267 : ℕ)^8461*20000000000000^6413 ≤ 2543246980839^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047418267 5000000000 2543246980839 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488431253/10000000000 : ℝ)^8461 ≤ (45314863613227/100000000000000 : ℝ)^6413 := by
    have hnat : (5488431253 : ℕ)^8461*100000000000000^6413 ≤ 45314863613227^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488431253 10000000000 45314863613227 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647304543/1250000000 : ℝ)^8461 ≤ (41968901473401/100000000000000 : ℝ)^6413 := by
    have hnat : (647304543 : ℕ)^8461*100000000000000^6413 ≤ 41968901473401^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647304543 1250000000 41968901473401 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047418267/5000000000 : ℝ), (5488431253/10000000000 : ℝ), (647304543/1250000000 : ℝ)] ![(2543246980839/20000000000000 : ℝ), (45314863613227/100000000000000 : ℝ), (41968901473401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047418267/5000000000 : ℝ)|^8461 ≤ (2543246980839/20000000000000 : ℝ)^6413
        have hw : |(-1047418267/5000000000 : ℝ)|=(1047418267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488431253/10000000000 : ℝ)|^8461 ≤ (45314863613227/100000000000000 : ℝ)^6413
        have hw : |(5488431253/10000000000 : ℝ)|=(5488431253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647304543/1250000000 : ℝ)|^8461 ≤ (41968901473401/100000000000000 : ℝ)^6413
        have hw : |(647304543/1250000000 : ℝ)|=(647304543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684320341/5000000000 : ℝ)*x 0 + (-2255268801/10000000000 : ℝ)*x 1 + (517843659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684320341/5000000000 : ℝ)^8461 ≤ (44014539094193/100000000000000 : ℝ)^6413 := by
    have hnat : (2684320341 : ℕ)^8461*100000000000000^6413 ≤ 44014539094193^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684320341 5000000000 44014539094193 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255268801/10000000000 : ℝ)^8461 ≤ (14016556780771/100000000000000 : ℝ)^6413 := by
    have hnat : (2255268801 : ℕ)^8461*100000000000000^6413 ≤ 14016556780771^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255268801 10000000000 14016556780771 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517843659/1000000000 : ℝ)^8461 ≤ (41968904103817/100000000000000 : ℝ)^6413 := by
    have hnat : (517843659 : ℕ)^8461*100000000000000^6413 ≤ 41968904103817^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517843659 1000000000 41968904103817 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684320341/5000000000 : ℝ), (-2255268801/10000000000 : ℝ), (517843659/1000000000 : ℝ)] ![(44014539094193/100000000000000 : ℝ), (14016556780771/100000000000000 : ℝ), (41968904103817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684320341/5000000000 : ℝ)|^8461 ≤ (44014539094193/100000000000000 : ℝ)^6413
        have hw : |(2684320341/5000000000 : ℝ)|=(2684320341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255268801/10000000000 : ℝ)|^8461 ≤ (14016556780771/100000000000000 : ℝ)^6413
        have hw : |(-2255268801/10000000000 : ℝ)|=(2255268801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517843659/1000000000 : ℝ)|^8461 ≤ (41968904103817/100000000000000 : ℝ)^6413
        have hw : |(517843659/1000000000 : ℝ)|=(517843659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684320317/5000000000 : ℝ)*x 0 + (2589218291/5000000000 : ℝ)*x 1 + (-563817219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684320317/5000000000 : ℝ)^8461 ≤ (8802907714999/20000000000000 : ℝ)^6413 := by
    have hnat : (2684320317 : ℕ)^8461*20000000000000^6413 ≤ 8802907714999^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684320317 5000000000 8802907714999 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589218291/5000000000 : ℝ)^8461 ≤ (1678756160731/4000000000000 : ℝ)^6413 := by
    have hnat : (2589218291 : ℕ)^8461*4000000000000^6413 ≤ 1678756160731^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589218291 5000000000 1678756160731 4000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563817219/2500000000 : ℝ)^8461 ≤ (3504139348939/25000000000000 : ℝ)^6413 := by
    have hnat : (563817219 : ℕ)^8461*25000000000000^6413 ≤ 3504139348939^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563817219 2500000000 3504139348939 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684320317/5000000000 : ℝ), (2589218291/5000000000 : ℝ), (-563817219/2500000000 : ℝ)] ![(8802907714999/20000000000000 : ℝ), (1678756160731/4000000000000 : ℝ), (3504139348939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684320317/5000000000 : ℝ)|^8461 ≤ (8802907714999/20000000000000 : ℝ)^6413
        have hw : |(2684320317/5000000000 : ℝ)|=(2684320317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589218291/5000000000 : ℝ)|^8461 ≤ (1678756160731/4000000000000 : ℝ)^6413
        have hw : |(2589218291/5000000000 : ℝ)|=(2589218291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563817219/2500000000 : ℝ)|^8461 ≤ (3504139348939/25000000000000 : ℝ)^6413
        have hw : |(-563817219/2500000000 : ℝ)|=(563817219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4338939967/10000000000 : ℝ)*x 0 + (2017009313/5000000000 : ℝ)*x 1 + (583252869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338939967/10000000000 : ℝ)^8461 ≤ (8308481134181/25000000000000 : ℝ)^6413 := by
    have hnat : (4338939967 : ℕ)^8461*25000000000000^6413 ≤ 8308481134181^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338939967 10000000000 8308481134181 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017009313/5000000000 : ℝ)^8461 ≤ (15093841391579/50000000000000 : ℝ)^6413 := by
    have hnat : (2017009313 : ℕ)^8461*50000000000000^6413 ≤ 15093841391579^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017009313 5000000000 15093841391579 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583252869/1250000000 : ℝ)^8461 ≤ (18289196332529/50000000000000 : ℝ)^6413 := by
    have hnat : (583252869 : ℕ)^8461*50000000000000^6413 ≤ 18289196332529^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583252869 1250000000 18289196332529 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338939967/10000000000 : ℝ), (2017009313/5000000000 : ℝ), (583252869/1250000000 : ℝ)] ![(8308481134181/25000000000000 : ℝ), (15093841391579/50000000000000 : ℝ), (18289196332529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338939967/10000000000 : ℝ)|^8461 ≤ (8308481134181/25000000000000 : ℝ)^6413
        have hw : |(4338939967/10000000000 : ℝ)|=(4338939967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017009313/5000000000 : ℝ)|^8461 ≤ (15093841391579/50000000000000 : ℝ)^6413
        have hw : |(2017009313/5000000000 : ℝ)|=(2017009313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(583252869/1250000000 : ℝ)|^8461 ≤ (18289196332529/50000000000000 : ℝ)^6413
        have hw : |(583252869/1250000000 : ℝ)|=(583252869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2094909717/10000000000 : ℝ)*x 0 + (5180393847/10000000000 : ℝ)*x 1 + (1371613931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094909717/10000000000 : ℝ)^8461 ≤ (397400656793/3125000000000 : ℝ)^6413 := by
    have hnat : (2094909717 : ℕ)^8461*3125000000000^6413 ≤ 397400656793^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094909717 10000000000 397400656793 3125000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180393847/10000000000 : ℝ)^8461 ≤ (5248729228371/12500000000000 : ℝ)^6413 := by
    have hnat : (5180393847 : ℕ)^8461*12500000000000^6413 ≤ 5248729228371^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180393847 10000000000 5248729228371 12500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371613931/2500000000 : ℝ)^8461 ≤ (45293345145187/100000000000000 : ℝ)^6413 := by
    have hnat : (1371613931 : ℕ)^8461*100000000000000^6413 ≤ 45293345145187^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371613931 2500000000 45293345145187 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2094909717/10000000000 : ℝ), (5180393847/10000000000 : ℝ), (1371613931/2500000000 : ℝ)] ![(397400656793/3125000000000 : ℝ), (5248729228371/12500000000000 : ℝ), (45293345145187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2094909717/10000000000 : ℝ)|^8461 ≤ (397400656793/3125000000000 : ℝ)^6413
        have hw : |(-2094909717/10000000000 : ℝ)|=(2094909717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180393847/10000000000 : ℝ)|^8461 ≤ (5248729228371/12500000000000 : ℝ)^6413
        have hw : |(5180393847/10000000000 : ℝ)|=(5180393847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371613931/2500000000 : ℝ)|^8461 ≤ (45293345145187/100000000000000 : ℝ)^6413
        have hw : |(1371613931/2500000000 : ℝ)|=(1371613931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289349369/10000000000 : ℝ)*x 0 + (-243406173/1250000000 : ℝ)*x 1 + (2743227883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289349369/10000000000 : ℝ)^8461 ≤ (43158903160943/100000000000000 : ℝ)^6413 := by
    have hnat : (5289349369 : ℕ)^8461*100000000000000^6413 ≤ 43158903160943^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289349369 10000000000 43158903160943 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243406173/1250000000 : ℝ)^8461 ≤ (5773875607473/50000000000000 : ℝ)^6413 := by
    have hnat : (243406173 : ℕ)^8461*50000000000000^6413 ≤ 5773875607473^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243406173 1250000000 5773875607473 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743227883/5000000000 : ℝ)^8461 ≤ (22646672801323/50000000000000 : ℝ)^6413 := by
    have hnat : (2743227883 : ℕ)^8461*50000000000000^6413 ≤ 22646672801323^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743227883 5000000000 22646672801323 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289349369/10000000000 : ℝ), (-243406173/1250000000 : ℝ), (2743227883/5000000000 : ℝ)] ![(43158903160943/100000000000000 : ℝ), (5773875607473/50000000000000 : ℝ), (22646672801323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289349369/10000000000 : ℝ)|^8461 ≤ (43158903160943/100000000000000 : ℝ)^6413
        have hw : |(5289349369/10000000000 : ℝ)|=(5289349369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243406173/1250000000 : ℝ)|^8461 ≤ (5773875607473/50000000000000 : ℝ)^6413
        have hw : |(-243406173/1250000000 : ℝ)|=(243406173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743227883/5000000000 : ℝ)|^8461 ≤ (22646672801323/50000000000000 : ℝ)^6413
        have hw : |(2743227883/5000000000 : ℝ)|=(2743227883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289349479/10000000000 : ℝ)*x 0 + (1097291177/2000000000 : ℝ)*x 1 + (-1947249067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289349479/10000000000 : ℝ)^8461 ≤ (43158904345133/100000000000000 : ℝ)^6413 := by
    have hnat : (5289349479 : ℕ)^8461*100000000000000^6413 ≤ 43158904345133^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289349479 10000000000 43158904345133 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097291177/2000000000 : ℝ)^8461 ≤ (2264667344939/5000000000000 : ℝ)^6413 := by
    have hnat : (1097291177 : ℕ)^8461*5000000000000^6413 ≤ 2264667344939^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097291177 2000000000 2264667344939 5000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947249067/10000000000 : ℝ)^8461 ≤ (2309549746939/20000000000000 : ℝ)^6413 := by
    have hnat : (1947249067 : ℕ)^8461*20000000000000^6413 ≤ 2309549746939^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947249067 10000000000 2309549746939 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289349479/10000000000 : ℝ), (1097291177/2000000000 : ℝ), (-1947249067/10000000000 : ℝ)] ![(43158904345133/100000000000000 : ℝ), (2264667344939/5000000000000 : ℝ), (2309549746939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289349479/10000000000 : ℝ)|^8461 ≤ (43158904345133/100000000000000 : ℝ)^6413
        have hw : |(5289349479/10000000000 : ℝ)|=(5289349479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097291177/2000000000 : ℝ)|^8461 ≤ (2264667344939/5000000000000 : ℝ)^6413
        have hw : |(1097291177/2000000000 : ℝ)|=(1097291177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947249067/10000000000 : ℝ)|^8461 ≤ (2309549746939/20000000000000 : ℝ)^6413
        have hw : |(-1947249067/10000000000 : ℝ)|=(1947249067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s2_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (433908877/1000000000 : ℝ)*x 0 + (4662032627/10000000000 : ℝ)*x 1 + (4038045277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433908877/1000000000 : ℝ)^8461 ≤ (830885706897/2500000000000 : ℝ)^6413 := by
    have hnat : (433908877 : ℕ)^8461*2500000000000^6413 ≤ 830885706897^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433908877 1000000000 830885706897 2500000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4662032627/10000000000 : ℝ)^8461 ≤ (18268563580633/50000000000000 : ℝ)^6413 := by
    have hnat : (4662032627 : ℕ)^8461*50000000000000^6413 ≤ 18268563580633^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662032627 10000000000 18268563580633 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038045277/10000000000 : ℝ)^8461 ≤ (7556861134013/25000000000000 : ℝ)^6413 := by
    have hnat : (4038045277 : ℕ)^8461*25000000000000^6413 ≤ 7556861134013^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038045277 10000000000 7556861134013 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433908877/1000000000 : ℝ), (4662032627/10000000000 : ℝ), (4038045277/10000000000 : ℝ)] ![(830885706897/2500000000000 : ℝ), (18268563580633/50000000000000 : ℝ), (7556861134013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433908877/1000000000 : ℝ)|^8461 ≤ (830885706897/2500000000000 : ℝ)^6413
        have hw : |(433908877/1000000000 : ℝ)|=(433908877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4662032627/10000000000 : ℝ)|^8461 ≤ (18268563580633/50000000000000 : ℝ)^6413
        have hw : |(4662032627/10000000000 : ℝ)|=(4662032627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038045277/10000000000 : ℝ)|^8461 ≤ (7556861134013/25000000000000 : ℝ)^6413
        have hw : |(4038045277/10000000000 : ℝ)|=(4038045277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1989/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3163/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9603/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4039/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1989/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3163/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1989/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3163/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1989/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3163/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1989/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3163/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1989/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3163/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1989/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3163/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3163/50000 : ℝ) ^ (2115/512 : ℝ) ≤ (8718129091831/781250000000000000 : ℝ) := by
    have hpowers : (3163/50000 : ℝ)^2115 ≤ (8718129091831/781250000000000000 : ℝ)^512 := by
      have hnat : (3163 : ℕ)^2115*781250000000000000^512 ≤ 8718129091831^512*50000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163 50000 8718129091831 781250000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3163/50000 : ℝ)) (X := (8718129091831/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1989/10000 : ℝ) ^ (2115/512 : ℝ) ≤ (15836854678322419/12500000000000000000 : ℝ) := by
    have hpowers : (1989/10000 : ℝ)^2115 ≤ (15836854678322419/12500000000000000000 : ℝ)^512 := by
      have hnat : (1989 : ℕ)^2115*12500000000000000000^512 ≤ 15836854678322419^512*10000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1989 10000 15836854678322419 12500000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1989/10000 : ℝ)) (X := (15836854678322419/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (390633718129091831/390625000000000000 : ℝ) ≤ (10000054028035543/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (390633718129091831/390625000000000000 : ℝ)^512 ≤ (10000054028035543/10000000000000000 : ℝ)^2115 := by
      have hnat : (390633718129091831 : ℕ)^512*10000000000000000^2115 ≤ 10000054028035543^2115*390625000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390633718129091831 390625000000000000 10000054028035543 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054028035543/10000000000000000 : ℝ)) (X := (390633718129091831/390625000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2503195268948758343/2500000000000000000 : ℝ) ≤ (10003092550177947/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (2503195268948758343/2500000000000000000 : ℝ)^512 ≤ (10003092550177947/10000000000000000 : ℝ)^2115 := by
      have hnat : (2503195268948758343 : ℕ)^512*10000000000000000^2115 ≤ 10003092550177947^2115*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2503195268948758343 2500000000000000000 10003092550177947 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003092550177947/10000000000000000 : ℝ)) (X := (2503195268948758343/2500000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6265836854678322419/6250000000000000000 : ℝ) ≤ (10006131072320351/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (6265836854678322419/6250000000000000000 : ℝ)^512 ≤ (10006131072320351/10000000000000000 : ℝ)^2115 := by
      have hnat : (6265836854678322419 : ℕ)^512*10000000000000000^2115 ≤ 10006131072320351^2115*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265836854678322419 6250000000000000000 10006131072320351 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006131072320351/10000000000000000 : ℝ)) (X := (6265836854678322419/6250000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8718129091831/781250000000000000 : ℝ) ≤ ((33900572363532102461/33910000000000000000 : ℝ)+2*(759630535601/339100000000000 : ℝ)*(3163/50000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (33900572363532102461/33910000000000000000 : ℝ)+2*(759630535601/339100000000000 : ℝ)*(3163/50000 : ℝ)=(10000054028035543/10000000000000000 : ℝ) by norm_num, show 1+2*(8718129091831/781250000000000000 : ℝ)=(390633718129091831/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15836854678322419/12500000000000000000 : ℝ)+(8718129091831/781250000000000000 : ℝ) ≤ ((33900572363532102461/33910000000000000000 : ℝ)+(759630535601/339100000000000 : ℝ)*((1989/10000 : ℝ)+(3163/50000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (33900572363532102461/33910000000000000000 : ℝ)+(759630535601/339100000000000 : ℝ)*((1989/10000 : ℝ)+(3163/50000 : ℝ))=(10003092550177947/10000000000000000 : ℝ) by norm_num, show 1+(15836854678322419/12500000000000000000 : ℝ)+(8718129091831/781250000000000000 : ℝ)=(2503195268948758343/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15836854678322419/12500000000000000000 : ℝ) ≤ ((33900572363532102461/33910000000000000000 : ℝ)+2*(759630535601/339100000000000 : ℝ)*(1989/10000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (33900572363532102461/33910000000000000000 : ℝ)+2*(759630535601/339100000000000 : ℝ)*(1989/10000 : ℝ)=(10006131072320351/10000000000000000 : ℝ) by norm_num, show 1+2*(15836854678322419/12500000000000000000 : ℝ)=(6265836854678322419/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33900572363532102461/33910000000000000000 : ℝ)*(X 1 0+X 2 0)+(759630535601/339100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (3163/50000 : ℝ)) (hi := (1989/10000 : ℝ)) (c := (33900572363532102461/33910000000000000000 : ℝ)) (alpha := (759630535601/339100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33900572363532102461/33910000000000000000 : ℝ)*(X 0 1+X 2 1)+(759630535601/339100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (3163/50000 : ℝ)) (hi := (1989/10000 : ℝ)) (c := (33900572363532102461/33910000000000000000 : ℝ)) (alpha := (759630535601/339100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33900572363532102461/33910000000000000000 : ℝ)*(X 0 2+X 1 2)+(759630535601/339100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (3163/50000 : ℝ)) (hi := (1989/10000 : ℝ)) (c := (33900572363532102461/33910000000000000000 : ℝ)) (alpha := (759630535601/339100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1047418267/5000000000 : ℝ)*X 0 0+(5488431253/10000000000 : ℝ)*X 0 1+(647304543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684320341/5000000000 : ℝ)*X 1 0+(-2255268801/10000000000 : ℝ)*X 1 1+(517843659/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684320317/5000000000 : ℝ)*X 2 0+(2589218291/5000000000 : ℝ)*X 2 1+(-563817219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338939967/10000000000 : ℝ)*X 0 0+(2017009313/5000000000 : ℝ)*X 0 1+(583252869/1250000000 : ℝ)*X 0 2+(4338939967/10000000000 : ℝ)*X 1 0+(2017009313/5000000000 : ℝ)*X 1 1+(583252869/1250000000 : ℝ)*X 1 2+(4338939967/10000000000 : ℝ)*X 2 0+(2017009313/5000000000 : ℝ)*X 2 1+(583252869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2094909717/10000000000 : ℝ)*X 0 0+(5180393847/10000000000 : ℝ)*X 0 1+(1371613931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289349369/10000000000 : ℝ)*X 1 0+(-243406173/1250000000 : ℝ)*X 1 1+(2743227883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289349479/10000000000 : ℝ)*X 2 0+(1097291177/2000000000 : ℝ)*X 2 1+(-1947249067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433908877/1000000000 : ℝ)*X 0 0+(4662032627/10000000000 : ℝ)*X 0 1+(4038045277/10000000000 : ℝ)*X 0 2+(433908877/1000000000 : ℝ)*X 1 0+(4662032627/10000000000 : ℝ)*X 1 1+(4038045277/10000000000 : ℝ)*X 1 2+(433908877/1000000000 : ℝ)*X 2 0+(4662032627/10000000000 : ℝ)*X 2 1+(4038045277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4033555944246621020176838943/423875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1751931313/100000000000000 : ℝ)*(base19) + (204748323/12500000000000 : ℝ)*(base23) + (45688497/100000000000000 : ℝ)*(lower2) + (130808607/50000000000000 : ℝ)*(upper3) + (131144723/100000000000000 : ℝ)*(upper5) + (601024121743893/25000000000000 : ℝ)*(major0) + (601024121743893/25000000000000 : ℝ)*(major1) + (601024121743893/25000000000000 : ℝ)*(major2) + (1612941507815231/50000000000000 : ℝ)*(sp0) + (403237846286859/12500000000000 : ℝ)*(sp1) + (8064757210599/250000000000 : ℝ)*(sp2) + (1582277185565009/100000000000000 : ℝ)*(sp3) + (21506595723/100000000000000 : ℝ)*(sp4) + (10948962977/100000000000000 : ℝ)*(sp7) + (791144067263993/50000000000000 : ℝ)*(f.failure) + (403238065278273/12500000000000 : ℝ)*(f.sum) + (29766987941999/8477500000000000000000000000 : ℝ)*base66 + (3002326593876320673/847750000000000000000000000000000 : ℝ)*base67 + (9115517886144570673/847750000000000000000000000000000 : ℝ)*base69 + (1003321736914570673/847750000000000000000000000000000 : ℝ)*base71 + (13237293630117/16955000000000000000000000000 : ℝ)*base73 + (2712812172119570673/847750000000000000000000000000000 : ℝ)*base75 + (6262149223630570673/847750000000000000000000000000000 : ℝ)*base77 + (5199947280175570673/847750000000000000000000000000000 : ℝ)*base79 + (333065986637/16955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (17778203/5000000000000000000000 : ℝ)*base89 + (17778203/5000000000000000000000 : ℝ)*base91 + (17778203/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9068279527291213771449/8477500000000000000000000000 : ℝ) := by norm_num
    linear_combination (607446813/100000000000000 : ℝ)*(base19) + (921239383/100000000000000 : ℝ)*(base23) + (9698769/12500000000000 : ℝ)*(upper2) + (55595447/50000000000000 : ℝ)*(upper3) + (567529/4000000000000 : ℝ)*(upper5) + (2434954154803603/100000000000000 : ℝ)*(major0) + (2434954154803603/100000000000000 : ℝ)*(major1) + (2434954154803603/100000000000000 : ℝ)*(major2) + (5736838163/100000000000000 : ℝ)*(sp1) + (12351117421/100000000000000 : ℝ)*(sp2) + (816827688550377/25000000000000 : ℝ)*(sp4) + (816826102479133/25000000000000 : ℝ)*(sp5) + (102103046307647/3125000000000 : ℝ)*(sp6) + (801298759874713/50000000000000 : ℝ)*(sp7) + (801298759874713/50000000000000 : ℝ)*(f.failure) + (816827688550377/25000000000000 : ℝ)*(f.sum) + (87808715417683/16955000000000000000000000000 : ℝ)*base65 + (14980450376629733017/3391000000000000000000000000000000 : ℝ)*base68 + (8248071153714266983/3391000000000000000000000000000000 : ℝ)*base69 + (20436787692014266983/3391000000000000000000000000000000 : ℝ)*base71 + (137055849849/8477500000000000000000000000 : ℝ)*base73 + (19360351789275733017/3391000000000000000000000000000000 : ℝ)*base76 + (3690745669518266983/3391000000000000000000000000000000 : ℝ)*base77 + (4669968337955733017/3391000000000000000000000000000000 : ℝ)*base80 + (65904750071113/16955000000000000000000000000 : ℝ)*base81 + (42572677/5000000000000000000000 : ℝ)*base90 + (42572677/5000000000000000000000 : ℝ)*base92 + (42572677/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1268_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1989/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3163/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1268_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1268_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1268_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1268_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
