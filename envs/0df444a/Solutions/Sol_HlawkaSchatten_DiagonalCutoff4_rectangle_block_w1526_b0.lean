-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1526_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:07.263282+00:00
-- url     : https://prove2.me/submissions/b6f5a322-e983-48a0-9586-f77951b0bf0b

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
theorem support_rectangle_w1526_s0_0 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-334217203/2000000000 : ℝ)*x 0 + (2951065167/5000000000 : ℝ)*x 1 + (151914377/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334217203/2000000000 : ℝ)^4549 ≤ (2484406869721/25000000000000 : ℝ)^3525 := by
    have hnat : (334217203 : ℕ)^4549*25000000000000^3525 ≤ 2484406869721^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334217203 2000000000 2484406869721 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2951065167/5000000000 : ℝ)^4549 ≤ (5063929639133/10000000000000 : ℝ)^3525 := by
    have hnat : (2951065167 : ℕ)^4549*10000000000000^3525 ≤ 5063929639133^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2951065167 5000000000 5063929639133 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151914377/312500000 : ℝ)^4549 ≤ (7884615223073/20000000000000 : ℝ)^3525 := by
    have hnat : (151914377 : ℕ)^4549*20000000000000^3525 ≤ 7884615223073^3525*312500000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151914377 312500000 7884615223073 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-334217203/2000000000 : ℝ), (2951065167/5000000000 : ℝ), (151914377/312500000 : ℝ)] ![(2484406869721/25000000000000 : ℝ), (5063929639133/10000000000000 : ℝ), (7884615223073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-334217203/2000000000 : ℝ)|^4549 ≤ (2484406869721/25000000000000 : ℝ)^3525
        have hw : |(-334217203/2000000000 : ℝ)|=(334217203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2951065167/5000000000 : ℝ)|^4549 ≤ (5063929639133/10000000000000 : ℝ)^3525
        have hw : |(2951065167/5000000000 : ℝ)|=(2951065167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151914377/312500000 : ℝ)|^4549 ≤ (7884615223073/20000000000000 : ℝ)^3525
        have hw : |(151914377/312500000 : ℝ)|=(151914377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_1 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5474940081/10000000000 : ℝ)*x 0 + (-450694091/2000000000 : ℝ)*x 1 + (2430629987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5474940081/10000000000 : ℝ)^4549 ≤ (9191989107723/20000000000000 : ℝ)^3525 := by
    have hnat : (5474940081 : ℕ)^4549*20000000000000^3525 ≤ 9191989107723^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474940081 10000000000 9191989107723 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450694091/2000000000 : ℝ)^4549 ≤ (7308489635937/50000000000000 : ℝ)^3525 := by
    have hnat : (450694091 : ℕ)^4549*50000000000000^3525 ≤ 7308489635937^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450694091 2000000000 7308489635937 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2430629987/5000000000 : ℝ)^4549 ≤ (39423075173473/100000000000000 : ℝ)^3525 := by
    have hnat : (2430629987 : ℕ)^4549*100000000000000^3525 ≤ 39423075173473^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430629987 5000000000 39423075173473 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5474940081/10000000000 : ℝ), (-450694091/2000000000 : ℝ), (2430629987/5000000000 : ℝ)] ![(9191989107723/20000000000000 : ℝ), (7308489635937/50000000000000 : ℝ), (39423075173473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5474940081/10000000000 : ℝ)|^4549 ≤ (9191989107723/20000000000000 : ℝ)^3525
        have hw : |(5474940081/10000000000 : ℝ)|=(5474940081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450694091/2000000000 : ℝ)|^4549 ≤ (7308489635937/50000000000000 : ℝ)^3525
        have hw : |(-450694091/2000000000 : ℝ)|=(450694091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2430629987/5000000000 : ℝ)|^4549 ≤ (39423075173473/100000000000000 : ℝ)^3525
        have hw : |(2430629987/5000000000 : ℝ)|=(2430629987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_2 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (684367527/1250000000 : ℝ)*x 0 + (4861260047/10000000000 : ℝ)*x 1 + (-2253470189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684367527/1250000000 : ℝ)^4549 ≤ (22979973500549/50000000000000 : ℝ)^3525 := by
    have hnat : (684367527 : ℕ)^4549*50000000000000^3525 ≤ 22979973500549^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684367527 1250000000 22979973500549 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4861260047/10000000000 : ℝ)^4549 ≤ (9855768984363/25000000000000 : ℝ)^3525 := by
    have hnat : (4861260047 : ℕ)^4549*25000000000000^3525 ≤ 9855768984363^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861260047 10000000000 9855768984363 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253470189/10000000000 : ℝ)^4549 ≤ (913561065329/6250000000000 : ℝ)^3525 := by
    have hnat : (2253470189 : ℕ)^4549*6250000000000^3525 ≤ 913561065329^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253470189 10000000000 913561065329 6250000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684367527/1250000000 : ℝ), (4861260047/10000000000 : ℝ), (-2253470189/10000000000 : ℝ)] ![(22979973500549/50000000000000 : ℝ), (9855768984363/25000000000000 : ℝ), (913561065329/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684367527/1250000000 : ℝ)|^4549 ≤ (22979973500549/50000000000000 : ℝ)^3525
        have hw : |(684367527/1250000000 : ℝ)|=(684367527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4861260047/10000000000 : ℝ)|^4549 ≤ (9855768984363/25000000000000 : ℝ)^3525
        have hw : |(4861260047/10000000000 : ℝ)|=(4861260047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253470189/10000000000 : ℝ)|^4549 ≤ (913561065329/6250000000000 : ℝ)^3525
        have hw : |(-2253470189/10000000000 : ℝ)|=(2253470189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_3 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035347457/2500000000 : ℝ)*x 0 + (3091469487/10000000000 : ℝ)*x 1 + (5475034761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035347457/2500000000 : ℝ)^4549 ≤ (32057408825629/100000000000000 : ℝ)^3525 := by
    have hnat : (1035347457 : ℕ)^4549*100000000000000^3525 ≤ 32057408825629^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035347457 2500000000 32057408825629 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091469487/10000000000 : ℝ)^4549 ≤ (10990809962939/50000000000000 : ℝ)^3525 := by
    have hnat : (3091469487 : ℕ)^4549*50000000000000^3525 ≤ 10990809962939^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091469487 10000000000 10990809962939 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475034761/10000000000 : ℝ)^4549 ≤ (22980485614507/50000000000000 : ℝ)^3525 := by
    have hnat : (5475034761 : ℕ)^4549*50000000000000^3525 ≤ 22980485614507^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475034761 10000000000 22980485614507 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035347457/2500000000 : ℝ), (3091469487/10000000000 : ℝ), (5475034761/10000000000 : ℝ)] ![(32057408825629/100000000000000 : ℝ), (10990809962939/50000000000000 : ℝ), (22980485614507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035347457/2500000000 : ℝ)|^4549 ≤ (32057408825629/100000000000000 : ℝ)^3525
        have hw : |(1035347457/2500000000 : ℝ)|=(1035347457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091469487/10000000000 : ℝ)|^4549 ≤ (10990809962939/50000000000000 : ℝ)^3525
        have hw : |(3091469487/10000000000 : ℝ)|=(3091469487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475034761/10000000000 : ℝ)|^4549 ≤ (22980485614507/50000000000000 : ℝ)^3525
        have hw : |(5475034761/10000000000 : ℝ)|=(5475034761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_4 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-334897589/2000000000 : ℝ)*x 0 + (2443868913/5000000000 : ℝ)*x 1 + (5874706681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334897589/2000000000 : ℝ)^4549 ≤ (9963742743619/100000000000000 : ℝ)^3525 := by
    have hnat : (334897589 : ℕ)^4549*100000000000000^3525 ≤ 9963742743619^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334897589 2000000000 9963742743619 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2443868913/5000000000 : ℝ)^4549 ≤ (39700397107729/100000000000000 : ℝ)^3525 := by
    have hnat : (2443868913 : ℕ)^4549*100000000000000^3525 ≤ 39700397107729^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2443868913 5000000000 39700397107729 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5874706681/10000000000 : ℝ)^4549 ≤ (6291982517137/12500000000000 : ℝ)^3525 := by
    have hnat : (5874706681 : ℕ)^4549*12500000000000^3525 ≤ 6291982517137^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5874706681 10000000000 6291982517137 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-334897589/2000000000 : ℝ), (2443868913/5000000000 : ℝ), (5874706681/10000000000 : ℝ)] ![(9963742743619/100000000000000 : ℝ), (39700397107729/100000000000000 : ℝ), (6291982517137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-334897589/2000000000 : ℝ)|^4549 ≤ (9963742743619/100000000000000 : ℝ)^3525
        have hw : |(-334897589/2000000000 : ℝ)|=(334897589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2443868913/5000000000 : ℝ)|^4549 ≤ (39700397107729/100000000000000 : ℝ)^3525
        have hw : |(2443868913/5000000000 : ℝ)|=(2443868913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5874706681/10000000000 : ℝ)|^4549 ≤ (6291982517137/12500000000000 : ℝ)^3525
        have hw : |(5874706681/10000000000 : ℝ)|=(5874706681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_5 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324406587/625000000 : ℝ)*x 0 + (-1240023763/10000000000 : ℝ)*x 1 + (734338311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324406587/625000000 : ℝ)^4549 ≤ (5362768771791/12500000000000 : ℝ)^3525 := by
    have hnat : (324406587 : ℕ)^4549*12500000000000^3525 ≤ 5362768771791^3525*625000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324406587 625000000 5362768771791 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240023763/10000000000 : ℝ)^4549 ≤ (169049795017/2500000000000 : ℝ)^3525 := by
    have hnat : (1240023763 : ℕ)^4549*2500000000000^3525 ≤ 169049795017^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240023763 10000000000 169049795017 2500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (734338311/1250000000 : ℝ)^4549 ≤ (25167929001521/50000000000000 : ℝ)^3525 := by
    have hnat : (734338311 : ℕ)^4549*50000000000000^3525 ≤ 25167929001521^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734338311 1250000000 25167929001521 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324406587/625000000 : ℝ), (-1240023763/10000000000 : ℝ), (734338311/1250000000 : ℝ)] ![(5362768771791/12500000000000 : ℝ), (169049795017/2500000000000 : ℝ), (25167929001521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324406587/625000000 : ℝ)|^4549 ≤ (5362768771791/12500000000000 : ℝ)^3525
        have hw : |(324406587/625000000 : ℝ)|=(324406587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1240023763/10000000000 : ℝ)|^4549 ≤ (169049795017/2500000000000 : ℝ)^3525
        have hw : |(-1240023763/10000000000 : ℝ)|=(1240023763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(734338311/1250000000 : ℝ)|^4549 ≤ (25167929001521/50000000000000 : ℝ)^3525
        have hw : |(734338311/1250000000 : ℝ)|=(734338311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_6 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1297626339/2500000000 : ℝ)*x 0 + (5874706417/10000000000 : ℝ)*x 1 + (-124002393/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297626339/2500000000 : ℝ)^4549 ≤ (42902149790331/100000000000000 : ℝ)^3525 := by
    have hnat : (1297626339 : ℕ)^4549*100000000000000^3525 ≤ 42902149790331^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297626339 2500000000 42902149790331 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5874706417/10000000000 : ℝ)^4549 ≤ (2013434288719/4000000000000 : ℝ)^3525 := by
    have hnat : (5874706417 : ℕ)^4549*4000000000000^3525 ≤ 2013434288719^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5874706417 10000000000 2013434288719 4000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124002393/1000000000 : ℝ)^4549 ≤ (845249121987/12500000000000 : ℝ)^3525 := by
    have hnat : (124002393 : ℕ)^4549*12500000000000^3525 ≤ 845249121987^3525*1000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124002393 1000000000 845249121987 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297626339/2500000000 : ℝ), (5874706417/10000000000 : ℝ), (-124002393/1000000000 : ℝ)] ![(42902149790331/100000000000000 : ℝ), (2013434288719/4000000000000 : ℝ), (845249121987/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297626339/2500000000 : ℝ)|^4549 ≤ (42902149790331/100000000000000 : ℝ)^3525
        have hw : |(1297626339/2500000000 : ℝ)|=(1297626339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5874706417/10000000000 : ℝ)|^4549 ≤ (2013434288719/4000000000000 : ℝ)^3525
        have hw : |(5874706417/10000000000 : ℝ)|=(5874706417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124002393/1000000000 : ℝ)|^4549 ≤ (845249121987/12500000000000 : ℝ)^3525
        have hw : |(-124002393/1000000000 : ℝ)|=(124002393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s0_7 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037295251/2500000000 : ℝ)*x 0 + (1082880331/2000000000 : ℝ)*x 1 + (1577134847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037295251/2500000000 : ℝ)^4549 ≤ (6427051841167/20000000000000 : ℝ)^3525 := by
    have hnat : (1037295251 : ℕ)^4549*20000000000000^3525 ≤ 6427051841167^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037295251 2500000000 6427051841167 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082880331/2000000000 : ℝ)^4549 ≤ (45305176440319/100000000000000 : ℝ)^3525 := by
    have hnat : (1082880331 : ℕ)^4549*100000000000000^3525 ≤ 45305176440319^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082880331 2000000000 45305176440319 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577134847/5000000000 : ℝ)^4549 ≤ (70498638551/312500000000 : ℝ)^3525 := by
    have hnat : (1577134847 : ℕ)^4549*312500000000^3525 ≤ 70498638551^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577134847 5000000000 70498638551 312500000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037295251/2500000000 : ℝ), (1082880331/2000000000 : ℝ), (1577134847/5000000000 : ℝ)] ![(6427051841167/20000000000000 : ℝ), (45305176440319/100000000000000 : ℝ), (70498638551/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037295251/2500000000 : ℝ)|^4549 ≤ (6427051841167/20000000000000 : ℝ)^3525
        have hw : |(1037295251/2500000000 : ℝ)|=(1037295251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082880331/2000000000 : ℝ)|^4549 ≤ (45305176440319/100000000000000 : ℝ)^3525
        have hw : |(1082880331/2000000000 : ℝ)|=(1082880331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577134847/5000000000 : ℝ)|^4549 ≤ (70498638551/312500000000 : ℝ)^3525
        have hw : |(1577134847/5000000000 : ℝ)|=(1577134847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1526_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1503/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3163/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4547/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4547 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4547*1^1024 ≤ 0^1024*1^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4547/1024 : ℝ) ≤ (427479586198936661/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4547 ≤ (427479586198936661/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4547*25000000000000000000^1024 ≤ 427479586198936661^1024*5^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 427479586198936661 25000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (427479586198936661/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4547 := by
      have hnat : (1 : ℕ)^1024*1^4547 ≤ 1^4547*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25427479586198936661/25000000000000000000 : ℝ) ≤ (2007651082763297/2000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (25427479586198936661/25000000000000000000 : ℝ)^1024 ≤ (2007651082763297/2000000000000000 : ℝ)^4547 := by
      have hnat : (25427479586198936661 : ℕ)^1024*2000000000000000^4547 ≤ 2007651082763297^4547*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25427479586198936661 25000000000000000000 2007651082763297 2000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2007651082763297/2000000000000000 : ℝ)) (X := (25427479586198936661/25000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12927479586198936661/12500000000000000000 : ℝ) ≤ (1007651082763297/1000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (12927479586198936661/12500000000000000000 : ℝ)^1024 ≤ (1007651082763297/1000000000000000 : ℝ)^4547 := by
      have hnat : (12927479586198936661 : ℕ)^1024*1000000000000000^4547 ≤ 1007651082763297^4547*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12927479586198936661 12500000000000000000 1007651082763297 1000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007651082763297/1000000000000000 : ℝ)) (X := (12927479586198936661/12500000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7651082763297/800000000000000 : ℝ)*(0 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7651082763297/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(427479586198936661/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7651082763297/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4547/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7651082763297/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2007651082763297/2000000000000000 : ℝ) by norm_num, show 1+(427479586198936661/25000000000000000000 : ℝ)+(0 : ℝ)=(25427479586198936661/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(427479586198936661/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7651082763297/800000000000000 : ℝ)*(2/5 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7651082763297/800000000000000 : ℝ)*(2/5 : ℝ)=(1007651082763297/1000000000000000 : ℝ) by norm_num, show 1+2*(427479586198936661/25000000000000000000 : ℝ)=(12927479586198936661/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7651082763297/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7651082763297/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7651082763297/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7651082763297/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7651082763297/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7651082763297/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-334217203/2000000000 : ℝ)*X 0 0+(2951065167/5000000000 : ℝ)*X 0 1+(151914377/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5474940081/10000000000 : ℝ)*X 1 0+(-450694091/2000000000 : ℝ)*X 1 1+(2430629987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((684367527/1250000000 : ℝ)*X 2 0+(4861260047/10000000000 : ℝ)*X 2 1+(-2253470189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1035347457/2500000000 : ℝ)*X 0 0+(3091469487/10000000000 : ℝ)*X 0 1+(5475034761/10000000000 : ℝ)*X 0 2+(1035347457/2500000000 : ℝ)*X 1 0+(3091469487/10000000000 : ℝ)*X 1 1+(5475034761/10000000000 : ℝ)*X 1 2+(1035347457/2500000000 : ℝ)*X 2 0+(3091469487/10000000000 : ℝ)*X 2 1+(5475034761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-334897589/2000000000 : ℝ)*X 0 0+(2443868913/5000000000 : ℝ)*X 0 1+(5874706681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324406587/625000000 : ℝ)*X 1 0+(-1240023763/10000000000 : ℝ)*X 1 1+(734338311/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1297626339/2500000000 : ℝ)*X 2 0+(5874706417/10000000000 : ℝ)*X 2 1+(-124002393/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037295251/2500000000 : ℝ)*X 0 0+(1082880331/2000000000 : ℝ)*X 0 1+(1577134847/5000000000 : ℝ)*X 0 2+(1037295251/2500000000 : ℝ)*X 1 0+(1082880331/2000000000 : ℝ)*X 1 1+(1577134847/5000000000 : ℝ)*X 1 2+(1037295251/2500000000 : ℝ)*X 2 0+(1082880331/2000000000 : ℝ)*X 2 1+(1577134847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89050024327818529268721/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053371/12500000000000 : ℝ)*(base1) + (1104172363/100000000000000 : ℝ)*(base19) + (140982767/12500000000000 : ℝ)*(base23) + (10331/9765625000 : ℝ)*(upper3) + (4731449/2500000000000 : ℝ)*(upper5) + (690142938916869/100000000000000 : ℝ)*(major0) + (690142938916869/100000000000000 : ℝ)*(major1) + (690142938916869/100000000000000 : ℝ)*(major2) + (480369051485059/50000000000000 : ℝ)*(sp0) + (480370709770621/50000000000000 : ℝ)*(sp1) + (96074139585147/10000000000000 : ℝ)*(sp2) + (104885364847027/25000000000000 : ℝ)*(sp3) + (553646307/12500000000000 : ℝ)*(sp4) + (1737888341/100000000000000 : ℝ)*(sp7) + (419543205703417/100000000000000 : ℝ)*(f.failure) + (480371261856803/50000000000000 : ℝ)*(f.sum) + (68717203437093/40000000000000000000000000000 : ℝ)*base65 + (404789245837093/80000000000000000000000000000 : ℝ)*base67 + (427814827042907/80000000000000000000000000000 : ℝ)*base70 + (424031856157093/80000000000000000000000000000 : ℝ)*base71 + (119258293717093/40000000000000000000000000000 : ℝ)*base73 + (563620083357093/80000000000000000000000000000 : ℝ)*base75 + (72559897282907/80000000000000000000000000000 : ℝ)*base78 + (555109964077093/80000000000000000000000000000 : ℝ)*base79 + (39068593122907/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (63189031/10000000000000000000000 : ℝ)*base90 + (63189031/10000000000000000000000 : ℝ)*base92 + (63189031/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98853185631719202477273/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125908317/12500000000000 : ℝ)*(base19) + (1003574737/100000000000000 : ℝ)*(base23) + (106682219/100000000000000 : ℝ)*(base32) + (145644539/100000000000000 : ℝ)*(upper3) + (10198943/12500000000000 : ℝ)*(upper5) + (363913679916397/50000000000000 : ℝ)*(major0) + (363913679916397/50000000000000 : ℝ)*(major1) + (363913679916397/50000000000000 : ℝ)*(major2) + (154378929/6250000000000 : ℝ)*(sp1) + (2530929293/100000000000000 : ℝ)*(sp2) + (202640539922941/20000000000000 : ℝ)*(sp4) + (126649902785663/12500000000000 : ℝ)*(sp5) + (506599582555337/50000000000000 : ℝ)*(sp6) + (8849034972267/2000000000000 : ℝ)*(sp7) + (442451855295569/100000000000000 : ℝ)*(f.failure) + (202640539922941/20000000000000 : ℝ)*(f.sum) + (16859256580909/20000000000000000000000000000 : ℝ)*base65 + (51246323119091/40000000000000000000000000000 : ℝ)*base68 + (233995660119091/40000000000000000000000000000 : ℝ)*base70 + (26805881999091/40000000000000000000000000000 : ℝ)*base72 + (45676056520909/20000000000000000000000000000 : ℝ)*base73 + (164663788560909/40000000000000000000000000000 : ℝ)*base75 + (47181874800909/40000000000000000000000000000 : ℝ)*base77 + (202692856920909/40000000000000000000000000000 : ℝ)*base79 + (19830093979091/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38550833/10000000000000000000000 : ℝ)*base89 + (38550833/10000000000000000000000 : ℝ)*base91 + (38550833/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1526_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3163/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1526_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1526_s1_0 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821070233/10000000000 : ℝ)*x 0 + (1112275013/2000000000 : ℝ)*x 1 + (2552778069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821070233/10000000000 : ℝ)^4549 ≤ (11103354950449/100000000000000 : ℝ)^3525 := by
    have hnat : (1821070233 : ℕ)^4549*100000000000000^3525 ≤ 11103354950449^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821070233 10000000000 11103354950449 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112275013/2000000000 : ℝ)^4549 ≤ (9379690525507/20000000000000 : ℝ)^3525 := by
    have hnat : (1112275013 : ℕ)^4549*20000000000000^3525 ≤ 9379690525507^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112275013 2000000000 9379690525507 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2552778069/5000000000 : ℝ)^4549 ≤ (5249774050787/12500000000000 : ℝ)^3525 := by
    have hnat : (2552778069 : ℕ)^4549*12500000000000^3525 ≤ 5249774050787^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552778069 5000000000 5249774050787 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821070233/10000000000 : ℝ), (1112275013/2000000000 : ℝ), (2552778069/5000000000 : ℝ)] ![(11103354950449/100000000000000 : ℝ), (9379690525507/20000000000000 : ℝ), (5249774050787/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821070233/10000000000 : ℝ)|^4549 ≤ (11103354950449/100000000000000 : ℝ)^3525
        have hw : |(-1821070233/10000000000 : ℝ)|=(1821070233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112275013/2000000000 : ℝ)|^4549 ≤ (9379690525507/20000000000000 : ℝ)^3525
        have hw : |(1112275013/2000000000 : ℝ)|=(1112275013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2552778069/5000000000 : ℝ)|^4549 ≤ (5249774050787/12500000000000 : ℝ)^3525
        have hw : |(2552778069/5000000000 : ℝ)|=(2552778069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_1 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384091769/10000000000 : ℝ)*x 0 + (-257584711/1250000000 : ℝ)*x 1 + (1276389451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384091769/10000000000 : ℝ)^4549 ≤ (11244537148049/25000000000000 : ℝ)^3525 := by
    have hnat : (5384091769 : ℕ)^4549*25000000000000^3525 ≤ 11244537148049^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384091769 10000000000 11244537148049 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257584711/1250000000 : ℝ)^4549 ≤ (13023641302803/100000000000000 : ℝ)^3525 := by
    have hnat : (257584711 : ℕ)^4549*100000000000000^3525 ≤ 13023641302803^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257584711 1250000000 13023641302803 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276389451/2500000000 : ℝ)^4549 ≤ (41998210091879/100000000000000 : ℝ)^3525 := by
    have hnat : (1276389451 : ℕ)^4549*100000000000000^3525 ≤ 41998210091879^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276389451 2500000000 41998210091879 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384091769/10000000000 : ℝ), (-257584711/1250000000 : ℝ), (1276389451/2500000000 : ℝ)] ![(11244537148049/25000000000000 : ℝ), (13023641302803/100000000000000 : ℝ), (41998210091879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384091769/10000000000 : ℝ)|^4549 ≤ (11244537148049/25000000000000 : ℝ)^3525
        have hw : |(5384091769/10000000000 : ℝ)|=(5384091769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257584711/1250000000 : ℝ)|^4549 ≤ (13023641302803/100000000000000 : ℝ)^3525
        have hw : |(-257584711/1250000000 : ℝ)|=(257584711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1276389451/2500000000 : ℝ)|^4549 ≤ (41998210091879/100000000000000 : ℝ)^3525
        have hw : |(1276389451/2500000000 : ℝ)|=(1276389451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_2 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346023313/2500000000 : ℝ)*x 0 + (2552777971/5000000000 : ℝ)*x 1 + (-2060678151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346023313/2500000000 : ℝ)^4549 ≤ (22489082289969/50000000000000 : ℝ)^3525 := by
    have hnat : (1346023313 : ℕ)^4549*50000000000000^3525 ≤ 22489082289969^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346023313 2500000000 22489082289969 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552777971/5000000000 : ℝ)^4549 ≤ (41998190325639/100000000000000 : ℝ)^3525 := by
    have hnat : (2552777971 : ℕ)^4549*100000000000000^3525 ≤ 41998190325639^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552777971 5000000000 41998190325639 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060678151/10000000000 : ℝ)^4549 ≤ (1627955634881/12500000000000 : ℝ)^3525 := by
    have hnat : (2060678151 : ℕ)^4549*12500000000000^3525 ≤ 1627955634881^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060678151 10000000000 1627955634881 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346023313/2500000000 : ℝ), (2552777971/5000000000 : ℝ), (-2060678151/10000000000 : ℝ)] ![(22489082289969/50000000000000 : ℝ), (41998190325639/100000000000000 : ℝ), (1627955634881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346023313/2500000000 : ℝ)|^4549 ≤ (22489082289969/50000000000000 : ℝ)^3525
        have hw : |(1346023313/2500000000 : ℝ)|=(1346023313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2552777971/5000000000 : ℝ)|^4549 ≤ (41998190325639/100000000000000 : ℝ)^3525
        have hw : |(2552777971/5000000000 : ℝ)|=(2552777971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060678151/10000000000 : ℝ)|^4549 ≤ (1627955634881/12500000000000 : ℝ)^3525
        have hw : |(-2060678151/10000000000 : ℝ)|=(2060678151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_3 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061125637/2500000000 : ℝ)*x 0 + (1874693247/5000000000 : ℝ)*x 1 + (299574867/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061125637/2500000000 : ℝ)^4549 ≤ (16545572834281/50000000000000 : ℝ)^3525 := by
    have hnat : (1061125637 : ℕ)^4549*50000000000000^3525 ≤ 16545572834281^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061125637 2500000000 16545572834281 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874693247/5000000000 : ℝ)^4549 ≤ (14098313608223/50000000000000 : ℝ)^3525 := by
    have hnat : (1874693247 : ℕ)^4549*50000000000000^3525 ≤ 14098313608223^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874693247 5000000000 14098313608223 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299574867/625000000 : ℝ)^4549 ≤ (9678056774609/25000000000000 : ℝ)^3525 := by
    have hnat : (299574867 : ℕ)^4549*25000000000000^3525 ≤ 9678056774609^3525*625000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299574867 625000000 9678056774609 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061125637/2500000000 : ℝ), (1874693247/5000000000 : ℝ), (299574867/625000000 : ℝ)] ![(16545572834281/50000000000000 : ℝ), (14098313608223/50000000000000 : ℝ), (9678056774609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061125637/2500000000 : ℝ)|^4549 ≤ (16545572834281/50000000000000 : ℝ)^3525
        have hw : |(1061125637/2500000000 : ℝ)|=(1061125637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1874693247/5000000000 : ℝ)|^4549 ≤ (14098313608223/50000000000000 : ℝ)^3525
        have hw : |(1874693247/5000000000 : ℝ)|=(1874693247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299574867/625000000 : ℝ)|^4549 ≤ (9678056774609/25000000000000 : ℝ)^3525
        have hw : |(299574867/625000000 : ℝ)|=(299574867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_4 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821347177/10000000000 : ℝ)*x 0 + (5110554677/10000000000 : ℝ)*x 1 + (5556297563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821347177/10000000000 : ℝ)^4549 ≤ (11105534094283/100000000000000 : ℝ)^3525 := by
    have hnat : (1821347177 : ℕ)^4549*100000000000000^3525 ≤ 11105534094283^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821347177 10000000000 11105534094283 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5110554677/10000000000 : ℝ)^4549 ≤ (42051262417959/100000000000000 : ℝ)^3525 := by
    have hnat : (5110554677 : ℕ)^4549*100000000000000^3525 ≤ 42051262417959^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5110554677 10000000000 42051262417959 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5556297563/10000000000 : ℝ)^4549 ≤ (23421601736359/50000000000000 : ℝ)^3525 := by
    have hnat : (5556297563 : ℕ)^4549*50000000000000^3525 ≤ 23421601736359^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556297563 10000000000 23421601736359 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821347177/10000000000 : ℝ), (5110554677/10000000000 : ℝ), (5556297563/10000000000 : ℝ)] ![(11105534094283/100000000000000 : ℝ), (42051262417959/100000000000000 : ℝ), (23421601736359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821347177/10000000000 : ℝ)|^4549 ≤ (11105534094283/100000000000000 : ℝ)^3525
        have hw : |(-1821347177/10000000000 : ℝ)|=(1821347177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5110554677/10000000000 : ℝ)|^4549 ≤ (42051262417959/100000000000000 : ℝ)^3525
        have hw : |(5110554677/10000000000 : ℝ)|=(5110554677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5556297563/10000000000 : ℝ)|^4549 ≤ (23421601736359/50000000000000 : ℝ)^3525
        have hw : |(5556297563/10000000000 : ℝ)|=(5556297563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_5 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263835973/10000000000 : ℝ)*x 0 + (-80496791/500000000 : ℝ)*x 1 + (2778148853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263835973/10000000000 : ℝ)^4549 ≤ (43685938295897/100000000000000 : ℝ)^3525 := by
    have hnat : (5263835973 : ℕ)^4549*100000000000000^3525 ≤ 43685938295897^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263835973 10000000000 43685938295897 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80496791/500000000 : ℝ)^4549 ≤ (1183857082317/12500000000000 : ℝ)^3525 := by
    have hnat : (80496791 : ℕ)^4549*12500000000000^3525 ≤ 1183857082317^3525*500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80496791 500000000 1183857082317 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2778148853/5000000000 : ℝ)^4549 ≤ (46843205028519/100000000000000 : ℝ)^3525 := by
    have hnat : (2778148853 : ℕ)^4549*100000000000000^3525 ≤ 46843205028519^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778148853 5000000000 46843205028519 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263835973/10000000000 : ℝ), (-80496791/500000000 : ℝ), (2778148853/5000000000 : ℝ)] ![(43685938295897/100000000000000 : ℝ), (1183857082317/12500000000000 : ℝ), (46843205028519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263835973/10000000000 : ℝ)|^4549 ≤ (43685938295897/100000000000000 : ℝ)^3525
        have hw : |(5263835973/10000000000 : ℝ)|=(5263835973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80496791/500000000 : ℝ)|^4549 ≤ (1183857082317/12500000000000 : ℝ)^3525
        have hw : |(-80496791/500000000 : ℝ)|=(80496791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2778148853/5000000000 : ℝ)|^4549 ≤ (46843205028519/100000000000000 : ℝ)^3525
        have hw : |(2778148853/5000000000 : ℝ)|=(2778148853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_6 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052767141/2000000000 : ℝ)*x 0 + (694537233/1250000000 : ℝ)*x 1 + (-402483993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052767141/2000000000 : ℝ)^4549 ≤ (43685935425573/100000000000000 : ℝ)^3525 := by
    have hnat : (1052767141 : ℕ)^4549*100000000000000^3525 ≤ 43685935425573^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052767141 2000000000 43685935425573 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694537233/1250000000 : ℝ)^4549 ≤ (11710801686879/25000000000000 : ℝ)^3525 := by
    have hnat : (694537233 : ℕ)^4549*25000000000000^3525 ≤ 11710801686879^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694537233 1250000000 11710801686879 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402483993/2500000000 : ℝ)^4549 ≤ (9470857812471/100000000000000 : ℝ)^3525 := by
    have hnat : (402483993 : ℕ)^4549*100000000000000^3525 ≤ 9470857812471^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402483993 2500000000 9470857812471 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052767141/2000000000 : ℝ), (694537233/1250000000 : ℝ), (-402483993/2500000000 : ℝ)] ![(43685935425573/100000000000000 : ℝ), (11710801686879/25000000000000 : ℝ), (9470857812471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052767141/2000000000 : ℝ)|^4549 ≤ (43685935425573/100000000000000 : ℝ)^3525
        have hw : |(1052767141/2000000000 : ℝ)|=(1052767141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(694537233/1250000000 : ℝ)|^4549 ≤ (11710801686879/25000000000000 : ℝ)^3525
        have hw : |(694537233/1250000000 : ℝ)|=(694537233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402483993/2500000000 : ℝ)|^4549 ≤ (9470857812471/100000000000000 : ℝ)^3525
        have hw : |(-402483993/2500000000 : ℝ)|=(402483993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s1_7 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245137371/10000000000 : ℝ)*x 0 + (597718967/1250000000 : ℝ)*x 1 + (3761011497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245137371/10000000000 : ℝ)^4549 ≤ (16548766385691/50000000000000 : ℝ)^3525 := by
    have hnat : (4245137371 : ℕ)^4549*50000000000000^3525 ≤ 16548766385691^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245137371 10000000000 16548766385691 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597718967/1250000000 : ℝ)^4549 ≤ (38592969030561/100000000000000 : ℝ)^3525 := by
    have hnat : (597718967 : ℕ)^4549*100000000000000^3525 ≤ 38592969030561^3525*1250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597718967 1250000000 38592969030561 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3761011497/10000000000 : ℝ)^4549 ≤ (1415474909039/5000000000000 : ℝ)^3525 := by
    have hnat : (3761011497 : ℕ)^4549*5000000000000^3525 ≤ 1415474909039^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761011497 10000000000 1415474909039 5000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245137371/10000000000 : ℝ), (597718967/1250000000 : ℝ), (3761011497/10000000000 : ℝ)] ![(16548766385691/50000000000000 : ℝ), (38592969030561/100000000000000 : ℝ), (1415474909039/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245137371/10000000000 : ℝ)|^4549 ≤ (16548766385691/50000000000000 : ℝ)^3525
        have hw : |(4245137371/10000000000 : ℝ)|=(4245137371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597718967/1250000000 : ℝ)|^4549 ≤ (38592969030561/100000000000000 : ℝ)^3525
        have hw : |(597718967/1250000000 : ℝ)|=(597718967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3761011497/10000000000 : ℝ)|^4549 ≤ (1415474909039/5000000000000 : ℝ)^3525
        have hw : |(3761011497/10000000000 : ℝ)|=(3761011497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1526_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (427/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2273/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3163/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3163/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3163/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3163/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3163/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3163/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1503/50000 : ℝ) ^ (4547/1024 : ℝ) ≤ (1744283471193/10000000000000000000 : ℝ) := by
    have hpowers : (1503/50000 : ℝ)^4547 ≤ (1744283471193/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1503 : ℕ)^4547*10000000000000000000^1024 ≤ 1744283471193^1024*50000^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1503 50000 1744283471193 10000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1503/50000 : ℝ)) (X := (1744283471193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3163/12500 : ℝ) ^ (4547/1024 : ℝ) ≤ (111911190703778281/50000000000000000000 : ℝ) := by
    have hpowers : (3163/12500 : ℝ)^4547 ≤ (111911190703778281/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3163 : ℕ)^4547*50000000000000000000^1024 ≤ 111911190703778281^1024*12500^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163 12500 111911190703778281 50000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3163/12500 : ℝ)) (X := (111911190703778281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000001744283471193/5000000000000000000 : ℝ) ≤ (5000000392818569/5000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (5000001744283471193/5000000000000000000 : ℝ)^1024 ≤ (5000000392818569/5000000000000000 : ℝ)^4547 := by
      have hnat : (5000001744283471193 : ℕ)^1024*5000000000000000^4547 ≤ 5000000392818569^4547*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000001744283471193 5000000000000000000 5000000392818569 5000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000392818569/5000000000000000 : ℝ)) (X := (5000001744283471193/5000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25055959956060567123/25000000000000000000 : ℝ) ≤ (10005036584149519/10000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (25055959956060567123/25000000000000000000 : ℝ)^1024 ≤ (10005036584149519/10000000000000000 : ℝ)^4547 := by
      have hnat : (25055959956060567123 : ℕ)^1024*10000000000000000^4547 ≤ 10005036584149519^4547*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25055959956060567123 25000000000000000000 10005036584149519 10000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005036584149519/10000000000000000 : ℝ)) (X := (25055959956060567123/25000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25111911190703778281/25000000000000000000 : ℝ) ≤ (100100723826619/100000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (25111911190703778281/25000000000000000000 : ℝ)^1024 ≤ (100100723826619/100000000000000 : ℝ)^4547 := by
      have hnat : (25111911190703778281 : ℕ)^1024*100000000000000^4547 ≤ 100100723826619^4547*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25111911190703778281 25000000000000000000 100100723826619 100000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100100723826619/100000000000000 : ℝ)) (X := (25111911190703778281/25000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1744283471193/10000000000000000000 : ℝ) ≤ ((27868717787185058569/27872500000000000000 : ℝ)+2*(5035798512381/2229800000000000 : ℝ)*(1503/50000 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (27868717787185058569/27872500000000000000 : ℝ)+2*(5035798512381/2229800000000000 : ℝ)*(1503/50000 : ℝ)=(5000000392818569/5000000000000000 : ℝ) by norm_num, show 1+2*(1744283471193/10000000000000000000 : ℝ)=(5000001744283471193/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(111911190703778281/50000000000000000000 : ℝ)+(1744283471193/10000000000000000000 : ℝ) ≤ ((27868717787185058569/27872500000000000000 : ℝ)+(5035798512381/2229800000000000 : ℝ)*((3163/12500 : ℝ)+(1503/50000 : ℝ)))^(4547/1024 : ℝ) := by
    rw [show (27868717787185058569/27872500000000000000 : ℝ)+(5035798512381/2229800000000000 : ℝ)*((3163/12500 : ℝ)+(1503/50000 : ℝ))=(10005036584149519/10000000000000000 : ℝ) by norm_num, show 1+(111911190703778281/50000000000000000000 : ℝ)+(1744283471193/10000000000000000000 : ℝ)=(25055959956060567123/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(111911190703778281/50000000000000000000 : ℝ) ≤ ((27868717787185058569/27872500000000000000 : ℝ)+2*(5035798512381/2229800000000000 : ℝ)*(3163/12500 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (27868717787185058569/27872500000000000000 : ℝ)+2*(5035798512381/2229800000000000 : ℝ)*(3163/12500 : ℝ)=(100100723826619/100000000000000 : ℝ) by norm_num, show 1+2*(111911190703778281/50000000000000000000 : ℝ)=(25111911190703778281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27868717787185058569/27872500000000000000 : ℝ)*(X 1 0+X 2 0)+(5035798512381/2229800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1503/50000 : ℝ)) (hi := (3163/12500 : ℝ)) (c := (27868717787185058569/27872500000000000000 : ℝ)) (alpha := (5035798512381/2229800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27868717787185058569/27872500000000000000 : ℝ)*(X 0 1+X 2 1)+(5035798512381/2229800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1503/50000 : ℝ)) (hi := (3163/12500 : ℝ)) (c := (27868717787185058569/27872500000000000000 : ℝ)) (alpha := (5035798512381/2229800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27868717787185058569/27872500000000000000 : ℝ)*(X 0 2+X 1 2)+(5035798512381/2229800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (1503/50000 : ℝ)) (hi := (3163/12500 : ℝ)) (c := (27868717787185058569/27872500000000000000 : ℝ)) (alpha := (5035798512381/2229800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1821070233/10000000000 : ℝ)*X 0 0+(1112275013/2000000000 : ℝ)*X 0 1+(2552778069/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5384091769/10000000000 : ℝ)*X 1 0+(-257584711/1250000000 : ℝ)*X 1 1+(1276389451/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1346023313/2500000000 : ℝ)*X 2 0+(2552777971/5000000000 : ℝ)*X 2 1+(-2060678151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061125637/2500000000 : ℝ)*X 0 0+(1874693247/5000000000 : ℝ)*X 0 1+(299574867/625000000 : ℝ)*X 0 2+(1061125637/2500000000 : ℝ)*X 1 0+(1874693247/5000000000 : ℝ)*X 1 1+(299574867/625000000 : ℝ)*X 1 2+(1061125637/2500000000 : ℝ)*X 2 0+(1874693247/5000000000 : ℝ)*X 2 1+(299574867/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1821347177/10000000000 : ℝ)*X 0 0+(5110554677/10000000000 : ℝ)*X 0 1+(5556297563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263835973/10000000000 : ℝ)*X 1 0+(-80496791/500000000 : ℝ)*X 1 1+(2778148853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052767141/2000000000 : ℝ)*X 2 0+(694537233/1250000000 : ℝ)*X 2 1+(-402483993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245137371/10000000000 : ℝ)*X 0 0+(597718967/1250000000 : ℝ)*X 0 1+(3761011497/10000000000 : ℝ)*X 0 2+(4245137371/10000000000 : ℝ)*X 1 0+(597718967/1250000000 : ℝ)*X 1 1+(3761011497/10000000000 : ℝ)*X 1 2+(4245137371/10000000000 : ℝ)*X 2 0+(597718967/1250000000 : ℝ)*X 2 1+(3761011497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552898152858107684030476359/55745000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37115661/100000000000000 : ℝ)*(base1) + (165711413/100000000000000 : ℝ)*(base19) + (384996021/50000000000000 : ℝ)*(base23) + (144805607/100000000000000 : ℝ)*(upper3) + (6149833/25000000000000 : ℝ)*(upper5) + (63037960346363/4000000000000 : ℝ)*(major0) + (63037960346363/4000000000000 : ℝ)*(major1) + (63037960346363/4000000000000 : ℝ)*(major2) + (219385991365153/10000000000000 : ℝ)*(sp0) + (438773197205417/20000000000000 : ℝ)*(sp1) + (274233172718307/12500000000000 : ℝ)*(sp2) + (239507195202857/25000000000000 : ℝ)*(sp3) + (627520263/10000000000000 : ℝ)*(sp4) + (54340821/2000000000000 : ℝ)*(sp7) + (47901576748407/5000000000000 : ℝ)*(f.failure) + (1096933075869249/50000000000000 : ℝ)*(f.sum) + (76775656637503/22298000000000000000000000000 : ℝ)*base65 + (649338076811157953/111490000000000000000000000000000 : ℝ)*base68 + (286787852679882047/111490000000000000000000000000000 : ℝ)*base69 + (373376944371012047/111490000000000000000000000000000 : ℝ)*base71 + (48615377194581/22298000000000000000000000000 : ℝ)*base74 + (354535920709982047/111490000000000000000000000000000 : ℝ)*base75 + (332688496395982047/111490000000000000000000000000000 : ℝ)*base77 + (76049984903237953/111490000000000000000000000000000 : ℝ)*base80 + (18857103063787/4459600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3389399/500000000000000000000 : ℝ)*base89 + (3389399/500000000000000000000 : ℝ)*base91 + (3389399/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2389095640904506624599741627/348406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1303073143/100000000000000 : ℝ)*(base19) + (266423051/20000000000000 : ℝ)*(base23) + (91643319/50000000000000 : ℝ)*(upper3) + (64677311/100000000000000 : ℝ)*(lower4) + (98310641/100000000000000 : ℝ)*(upper5) + (402890657001437/25000000000000 : ℝ)*(major0) + (402890657001437/25000000000000 : ℝ)*(major1) + (402890657001437/25000000000000 : ℝ)*(major2) + (2372995583/25000000000000 : ℝ)*(sp1) + (5192224037/50000000000000 : ℝ)*(sp2) + (2243443699093679/100000000000000 : ℝ)*(sp4) + (560858226009551/25000000000000 : ℝ)*(sp5) + (44868639650607/2000000000000 : ℝ)*(sp6) + (489840664172033/50000000000000 : ℝ)*(sp7) + (489840664172033/50000000000000 : ℝ)*(f.failure) + (2243443699093679/100000000000000 : ℝ)*(f.sum) + (147540227172259/55745000000000000000000000000 : ℝ)*base65 + (4359093774881061347/696812500000000000000000000000000 : ℝ)*base68 + (7950567009079811347/696812500000000000000000000000000 : ℝ)*base70 + (4246658219132498847/696812500000000000000000000000000 : ℝ)*base72 + (23020670681303/27872500000000000000000000000 : ℝ)*base74 + (6318544806053248847/696812500000000000000000000000000 : ℝ)*base76 + (6440088507388873847/696812500000000000000000000000000 : ℝ)*base78 + (1395370034088873847/696812500000000000000000000000000 : ℝ)*base80 + (78069486650433/27872500000000000000000000000 : ℝ)*base82 + (45459681/5000000000000000000000 : ℝ)*base89 + (45459681/5000000000000000000000 : ℝ)*base91 + (45459681/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1526_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (427/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2273/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1526_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1526_s2_0 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844024481/10000000000 : ℝ)*x 0 + (5453571751/10000000000 : ℝ)*x 1 + (2599234493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844024481/10000000000 : ℝ)^4549 ≤ (11284296977207/100000000000000 : ℝ)^3525 := by
    have hnat : (1844024481 : ℕ)^4549*100000000000000^3525 ≤ 11284296977207^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844024481 10000000000 11284296977207 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453571751/10000000000 : ℝ)^4549 ≤ (5716073674427/12500000000000 : ℝ)^3525 := by
    have hnat : (5453571751 : ℕ)^4549*12500000000000^3525 ≤ 5716073674427^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453571751 10000000000 5716073674427 12500000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599234493/5000000000 : ℝ)^4549 ≤ (21493556805869/50000000000000 : ℝ)^3525 := by
    have hnat : (2599234493 : ℕ)^4549*50000000000000^3525 ≤ 21493556805869^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599234493 5000000000 21493556805869 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844024481/10000000000 : ℝ), (5453571751/10000000000 : ℝ), (2599234493/5000000000 : ℝ)] ![(11284296977207/100000000000000 : ℝ), (5716073674427/12500000000000 : ℝ), (21493556805869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844024481/10000000000 : ℝ)|^4549 ≤ (11284296977207/100000000000000 : ℝ)^3525
        have hw : |(-1844024481/10000000000 : ℝ)|=(1844024481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453571751/10000000000 : ℝ)|^4549 ≤ (5716073674427/12500000000000 : ℝ)^3525
        have hw : |(5453571751/10000000000 : ℝ)|=(5453571751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599234493/5000000000 : ℝ)|^4549 ≤ (21493556805869/50000000000000 : ℝ)^3525
        have hw : |(2599234493/5000000000 : ℝ)|=(2599234493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_1 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339146193/2500000000 : ℝ)*x 0 + (-987620611/5000000000 : ℝ)*x 1 + (2599234723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339146193/2500000000 : ℝ)^4549 ≤ (22340912465049/50000000000000 : ℝ)^3525 := by
    have hnat : (1339146193 : ℕ)^4549*50000000000000^3525 ≤ 22340912465049^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339146193 2500000000 22340912465049 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987620611/5000000000 : ℝ)^4549 ≤ (2466211307971/20000000000000 : ℝ)^3525 := by
    have hnat : (987620611 : ℕ)^4549*20000000000000^3525 ≤ 2466211307971^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987620611 5000000000 2466211307971 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599234723/5000000000 : ℝ)^4549 ≤ (21493559260281/50000000000000 : ℝ)^3525 := by
    have hnat : (2599234723 : ℕ)^4549*50000000000000^3525 ≤ 21493559260281^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599234723 5000000000 21493559260281 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339146193/2500000000 : ℝ), (-987620611/5000000000 : ℝ), (2599234723/5000000000 : ℝ)] ![(22340912465049/50000000000000 : ℝ), (2466211307971/20000000000000 : ℝ), (21493559260281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339146193/2500000000 : ℝ)|^4549 ≤ (22340912465049/50000000000000 : ℝ)^3525
        have hw : |(1339146193/2500000000 : ℝ)|=(1339146193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987620611/5000000000 : ℝ)|^4549 ≤ (2466211307971/20000000000000 : ℝ)^3525
        have hw : |(-987620611/5000000000 : ℝ)|=(987620611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599234723/5000000000 : ℝ)|^4549 ≤ (21493559260281/50000000000000 : ℝ)^3525
        have hw : |(2599234723/5000000000 : ℝ)|=(2599234723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_2 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678292759/5000000000 : ℝ)*x 0 + (5198468997/10000000000 : ℝ)*x 1 + (-1975240819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678292759/5000000000 : ℝ)^4549 ≤ (11170458240131/25000000000000 : ℝ)^3525 := by
    have hnat : (2678292759 : ℕ)^4549*25000000000000^3525 ≤ 11170458240131^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678292759 5000000000 11170458240131 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198468997/10000000000 : ℝ)^4549 ≤ (42987113729123/100000000000000 : ℝ)^3525 := by
    have hnat : (5198468997 : ℕ)^4549*100000000000000^3525 ≤ 42987113729123^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198468997 10000000000 42987113729123 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975240819/10000000000 : ℝ)^4549 ≤ (12331053293157/100000000000000 : ℝ)^3525 := by
    have hnat : (1975240819 : ℕ)^4549*100000000000000^3525 ≤ 12331053293157^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975240819 10000000000 12331053293157 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678292759/5000000000 : ℝ), (5198468997/10000000000 : ℝ), (-1975240819/10000000000 : ℝ)] ![(11170458240131/25000000000000 : ℝ), (42987113729123/100000000000000 : ℝ), (12331053293157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678292759/5000000000 : ℝ)|^4549 ≤ (11170458240131/25000000000000 : ℝ)^3525
        have hw : |(2678292759/5000000000 : ℝ)|=(2678292759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198468997/10000000000 : ℝ)|^4549 ≤ (42987113729123/100000000000000 : ℝ)^3525
        have hw : |(5198468997/10000000000 : ℝ)|=(5198468997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975240819/10000000000 : ℝ)|^4549 ≤ (12331053293157/100000000000000 : ℝ)^3525
        have hw : |(-1975240819/10000000000 : ℝ)|=(1975240819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_3 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130510713/5000000000 : ℝ)*x 0 + (3977326349/10000000000 : ℝ)*x 1 + (71273533/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130510713/5000000000 : ℝ)^4549 ≤ (33257436218547/100000000000000 : ℝ)^3525 := by
    have hnat : (2130510713 : ℕ)^4549*100000000000000^3525 ≤ 33257436218547^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130510713 5000000000 33257436218547 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3977326349/10000000000 : ℝ)^4549 ≤ (15214017206813/50000000000000 : ℝ)^3525 := by
    have hnat : (3977326349 : ℕ)^4549*50000000000000^3525 ≤ 15214017206813^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977326349 10000000000 15214017206813 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71273533/156250000 : ℝ)^4549 ≤ (3631452934091/10000000000000 : ℝ)^3525 := by
    have hnat : (71273533 : ℕ)^4549*10000000000000^3525 ≤ 3631452934091^3525*156250000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71273533 156250000 3631452934091 10000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130510713/5000000000 : ℝ), (3977326349/10000000000 : ℝ), (71273533/156250000 : ℝ)] ![(33257436218547/100000000000000 : ℝ), (15214017206813/50000000000000 : ℝ), (3631452934091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130510713/5000000000 : ℝ)|^4549 ≤ (33257436218547/100000000000000 : ℝ)^3525
        have hw : |(2130510713/5000000000 : ℝ)|=(2130510713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3977326349/10000000000 : ℝ)|^4549 ≤ (15214017206813/50000000000000 : ℝ)^3525
        have hw : |(3977326349/10000000000 : ℝ)|=(3977326349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71273533/156250000 : ℝ)|^4549 ≤ (3631452934091/10000000000000 : ℝ)^3525
        have hw : |(71273533/156250000 : ℝ)|=(71273533/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_4 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844071769/10000000000 : ℝ)*x 0 + (5200043993/10000000000 : ℝ)*x 1 + (1090396773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844071769/10000000000 : ℝ)^4549 ≤ (2256934082817/20000000000000 : ℝ)^3525 := by
    have hnat : (1844071769 : ℕ)^4549*20000000000000^3525 ≤ 2256934082817^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844071769 10000000000 2256934082817 20000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200043993/10000000000 : ℝ)^4549 ≤ (43003921813079/100000000000000 : ℝ)^3525 := by
    have hnat : (5200043993 : ℕ)^4549*100000000000000^3525 ≤ 43003921813079^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200043993 10000000000 43003921813079 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090396773/2000000000 : ℝ)^4549 ≤ (11427851939597/25000000000000 : ℝ)^3525 := by
    have hnat : (1090396773 : ℕ)^4549*25000000000000^3525 ≤ 11427851939597^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090396773 2000000000 11427851939597 25000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844071769/10000000000 : ℝ), (5200043993/10000000000 : ℝ), (1090396773/2000000000 : ℝ)] ![(2256934082817/20000000000000 : ℝ), (43003921813079/100000000000000 : ℝ), (11427851939597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844071769/10000000000 : ℝ)|^4549 ≤ (2256934082817/20000000000000 : ℝ)^3525
        have hw : |(-1844071769/10000000000 : ℝ)|=(1844071769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200043993/10000000000 : ℝ)|^4549 ≤ (43003921813079/100000000000000 : ℝ)^3525
        have hw : |(5200043993/10000000000 : ℝ)|=(5200043993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090396773/2000000000 : ℝ)|^4549 ≤ (11427851939597/25000000000000 : ℝ)^3525
        have hw : |(1090396773/2000000000 : ℝ)|=(1090396773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_5 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057892887/2000000000 : ℝ)*x 0 + (-860863611/5000000000 : ℝ)*x 1 + (136299623/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057892887/2000000000 : ℝ)^4549 ≤ (43960617224073/100000000000000 : ℝ)^3525 := by
    have hnat : (1057892887 : ℕ)^4549*100000000000000^3525 ≤ 43960617224073^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057892887 2000000000 43960617224073 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860863611/5000000000 : ℝ)^4549 ≤ (10327963584571/100000000000000 : ℝ)^3525 := by
    have hnat : (860863611 : ℕ)^4549*100000000000000^3525 ≤ 10327963584571^3525*5000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860863611 5000000000 10327963584571 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136299623/250000000 : ℝ)^4549 ≤ (45711419173477/100000000000000 : ℝ)^3525 := by
    have hnat : (136299623 : ℕ)^4549*100000000000000^3525 ≤ 45711419173477^3525*250000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136299623 250000000 45711419173477 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057892887/2000000000 : ℝ), (-860863611/5000000000 : ℝ), (136299623/250000000 : ℝ)] ![(43960617224073/100000000000000 : ℝ), (10327963584571/100000000000000 : ℝ), (45711419173477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057892887/2000000000 : ℝ)|^4549 ≤ (43960617224073/100000000000000 : ℝ)^3525
        have hw : |(1057892887/2000000000 : ℝ)|=(1057892887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-860863611/5000000000 : ℝ)|^4549 ≤ (10327963584571/100000000000000 : ℝ)^3525
        have hw : |(-860863611/5000000000 : ℝ)|=(860863611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136299623/250000000 : ℝ)|^4549 ≤ (45711419173477/100000000000000 : ℝ)^3525
        have hw : |(136299623/250000000 : ℝ)|=(136299623/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_6 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057893057/2000000000 : ℝ)*x 0 + (1362996201/2500000000 : ℝ)*x 1 + (-1721726207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057893057/2000000000 : ℝ)^4549 ≤ (21980313170283/50000000000000 : ℝ)^3525 := by
    have hnat : (1057893057 : ℕ)^4549*50000000000000^3525 ≤ 21980313170283^3525*2000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057893057 2000000000 21980313170283 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362996201/2500000000 : ℝ)^4549 ≤ (22855708959179/50000000000000 : ℝ)^3525 := by
    have hnat : (1362996201 : ℕ)^4549*50000000000000^3525 ≤ 22855708959179^3525*2500000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362996201 2500000000 22855708959179 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1721726207/10000000000 : ℝ)^4549 ≤ (5163977863637/50000000000000 : ℝ)^3525 := by
    have hnat : (1721726207 : ℕ)^4549*50000000000000^3525 ≤ 5163977863637^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721726207 10000000000 5163977863637 50000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057893057/2000000000 : ℝ), (1362996201/2500000000 : ℝ), (-1721726207/10000000000 : ℝ)] ![(21980313170283/50000000000000 : ℝ), (22855708959179/50000000000000 : ℝ), (5163977863637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057893057/2000000000 : ℝ)|^4549 ≤ (21980313170283/50000000000000 : ℝ)^3525
        have hw : |(1057893057/2000000000 : ℝ)|=(1057893057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362996201/2500000000 : ℝ)|^4549 ≤ (22855708959179/50000000000000 : ℝ)^3525
        have hw : |(1362996201/2500000000 : ℝ)|=(1362996201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1721726207/10000000000 : ℝ)|^4549 ≤ (5163977863637/50000000000000 : ℝ)^3525
        have hw : |(-1721726207/10000000000 : ℝ)|=(1721726207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1526_s2_7 (p : ℝ) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261133543/10000000000 : ℝ)*x 0 + (4557901423/10000000000 : ℝ)*x 1 + (3980962141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261133543/10000000000 : ℝ)^4549 ≤ (33258565507273/100000000000000 : ℝ)^3525 := by
    have hnat : (4261133543 : ℕ)^4549*100000000000000^3525 ≤ 33258565507273^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261133543 10000000000 33258565507273 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557901423/10000000000 : ℝ)^4549 ≤ (36277499920499/100000000000000 : ℝ)^3525 := by
    have hnat : (4557901423 : ℕ)^4549*100000000000000^3525 ≤ 36277499920499^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557901423 10000000000 36277499920499 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3980962141/10000000000 : ℝ)^4549 ≤ (30463934555437/100000000000000 : ℝ)^3525 := by
    have hnat : (3980962141 : ℕ)^4549*100000000000000^3525 ≤ 30463934555437^3525*10000000000^4549 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980962141 10000000000 30463934555437 100000000000000 4549 3525 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4549/1024 : ℝ)) 4549 3525 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261133543/10000000000 : ℝ), (4557901423/10000000000 : ℝ), (3980962141/10000000000 : ℝ)] ![(33258565507273/100000000000000 : ℝ), (36277499920499/100000000000000 : ℝ), (30463934555437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261133543/10000000000 : ℝ)|^4549 ≤ (33258565507273/100000000000000 : ℝ)^3525
        have hw : |(4261133543/10000000000 : ℝ)|=(4261133543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557901423/10000000000 : ℝ)|^4549 ≤ (36277499920499/100000000000000 : ℝ)^3525
        have hw : |(4557901423/10000000000 : ℝ)|=(4557901423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3980962141/10000000000 : ℝ)|^4549 ≤ (30463934555437/100000000000000 : ℝ)^3525
        have hw : |(3980962141/10000000000 : ℝ)|=(3980962141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1526_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2273/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (427/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (659/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7973/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2273/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (427/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2273/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (427/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2273/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (427/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2273/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (427/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2273/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (427/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2273/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (427/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (427/5000 : ℝ) ^ (4547/1024 : ℝ) ≤ (899878365881827/50000000000000000000 : ℝ) := by
    have hpowers : (427/5000 : ℝ)^4547 ≤ (899878365881827/50000000000000000000 : ℝ)^1024 := by
      have hnat : (427 : ℕ)^4547*50000000000000000000^1024 ≤ 899878365881827^1024*5000^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        427 5000 899878365881827 50000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (427/5000 : ℝ)) (X := (899878365881827/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2273/12500 : ℝ) ^ (4547/1024 : ℝ) ≤ (10321265036999813/20000000000000000000 : ℝ) := by
    have hpowers : (2273/12500 : ℝ)^4547 ≤ (10321265036999813/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2273 : ℕ)^4547*20000000000000000000^1024 ≤ 10321265036999813^1024*12500^4547 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 12500 10321265036999813 20000000000000000000 4547 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/12500 : ℝ)) (X := (10321265036999813/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000899878365881827/25000000000000000000 : ℝ) ≤ (10000081061147787/10000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (25000899878365881827/25000000000000000000 : ℝ)^1024 ≤ (10000081061147787/10000000000000000 : ℝ)^4547 := by
      have hnat : (25000899878365881827 : ℕ)^1024*10000000000000000^4547 ≤ 10000081061147787^4547*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000899878365881827 25000000000000000000 10000081061147787 10000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081061147787/10000000000000000 : ℝ)) (X := (25000899878365881827/25000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053406081916762719/100000000000000000000 : ℝ) ≤ (312537577329049/312500000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (100053406081916762719/100000000000000000000 : ℝ)^1024 ≤ (312537577329049/312500000000000 : ℝ)^4547 := by
      have hnat : (100053406081916762719 : ℕ)^1024*312500000000000^4547 ≤ 312537577329049^4547*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053406081916762719 100000000000000000000 312537577329049 312500000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312537577329049/312500000000000 : ℝ)) (X := (100053406081916762719/100000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010321265036999813/10000000000000000000 : ℝ) ≤ (10002323887911349/10000000000000000 : ℝ) ^ (4547/1024 : ℝ) := by
    have hpowers : (10010321265036999813/10000000000000000000 : ℝ)^1024 ≤ (10002323887911349/10000000000000000 : ℝ)^4547 := by
      have hnat : (10010321265036999813 : ℕ)^1024*10000000000000000^4547 ≤ 10002323887911349^4547*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010321265036999813 10000000000000000000 10002323887911349 10000000000000000 1024 4547 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002323887911349/10000000000000000 : ℝ)) (X := (10010321265036999813/10000000000000000000 : ℝ)) (by norm_num) 4547 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(899878365881827/50000000000000000000 : ℝ) ≤ ((24105407003287109587/24110000000000000000 : ℝ)+2*(1121413381781/964400000000000 : ℝ)*(427/5000 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (24105407003287109587/24110000000000000000 : ℝ)+2*(1121413381781/964400000000000 : ℝ)*(427/5000 : ℝ)=(10000081061147787/10000000000000000 : ℝ) by norm_num, show 1+2*(899878365881827/50000000000000000000 : ℝ)=(25000899878365881827/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10321265036999813/20000000000000000000 : ℝ)+(899878365881827/50000000000000000000 : ℝ) ≤ ((24105407003287109587/24110000000000000000 : ℝ)+(1121413381781/964400000000000 : ℝ)*((2273/12500 : ℝ)+(427/5000 : ℝ)))^(4547/1024 : ℝ) := by
    rw [show (24105407003287109587/24110000000000000000 : ℝ)+(1121413381781/964400000000000 : ℝ)*((2273/12500 : ℝ)+(427/5000 : ℝ))=(312537577329049/312500000000000 : ℝ) by norm_num, show 1+(10321265036999813/20000000000000000000 : ℝ)+(899878365881827/50000000000000000000 : ℝ)=(100053406081916762719/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10321265036999813/20000000000000000000 : ℝ) ≤ ((24105407003287109587/24110000000000000000 : ℝ)+2*(1121413381781/964400000000000 : ℝ)*(2273/12500 : ℝ))^(4547/1024 : ℝ) := by
    rw [show (24105407003287109587/24110000000000000000 : ℝ)+2*(1121413381781/964400000000000 : ℝ)*(2273/12500 : ℝ)=(10002323887911349/10000000000000000 : ℝ) by norm_num, show 1+2*(10321265036999813/20000000000000000000 : ℝ)=(10010321265036999813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24105407003287109587/24110000000000000000 : ℝ)*(X 1 0+X 2 0)+(1121413381781/964400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (427/5000 : ℝ)) (hi := (2273/12500 : ℝ)) (c := (24105407003287109587/24110000000000000000 : ℝ)) (alpha := (1121413381781/964400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24105407003287109587/24110000000000000000 : ℝ)*(X 0 1+X 2 1)+(1121413381781/964400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (427/5000 : ℝ)) (hi := (2273/12500 : ℝ)) (c := (24105407003287109587/24110000000000000000 : ℝ)) (alpha := (1121413381781/964400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24105407003287109587/24110000000000000000 : ℝ)*(X 0 2+X 1 2)+(1121413381781/964400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4547/1024 : ℝ)) (lo := (427/5000 : ℝ)) (hi := (2273/12500 : ℝ)) (c := (24105407003287109587/24110000000000000000 : ℝ)) (alpha := (1121413381781/964400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1844024481/10000000000 : ℝ)*X 0 0+(5453571751/10000000000 : ℝ)*X 0 1+(2599234493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339146193/2500000000 : ℝ)*X 1 0+(-987620611/5000000000 : ℝ)*X 1 1+(2599234723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678292759/5000000000 : ℝ)*X 2 0+(5198468997/10000000000 : ℝ)*X 2 1+(-1975240819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130510713/5000000000 : ℝ)*X 0 0+(3977326349/10000000000 : ℝ)*X 0 1+(71273533/156250000 : ℝ)*X 0 2+(2130510713/5000000000 : ℝ)*X 1 0+(3977326349/10000000000 : ℝ)*X 1 1+(71273533/156250000 : ℝ)*X 1 2+(2130510713/5000000000 : ℝ)*X 2 0+(3977326349/10000000000 : ℝ)*X 2 1+(71273533/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1844071769/10000000000 : ℝ)*X 0 0+(5200043993/10000000000 : ℝ)*X 0 1+(1090396773/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057892887/2000000000 : ℝ)*X 1 0+(-860863611/5000000000 : ℝ)*X 1 1+(136299623/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057893057/2000000000 : ℝ)*X 2 0+(1362996201/2500000000 : ℝ)*X 2 1+(-1721726207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261133543/10000000000 : ℝ)*X 0 0+(4557901423/10000000000 : ℝ)*X 0 1+(3980962141/10000000000 : ℝ)*X 0 2+(4261133543/10000000000 : ℝ)*X 1 0+(4557901423/10000000000 : ℝ)*X 1 1+(3980962141/10000000000 : ℝ)*X 1 2+(4261133543/10000000000 : ℝ)*X 2 0+(4557901423/10000000000 : ℝ)*X 2 1+(3980962141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1526_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1296705678609423200718792027/602750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44730371/6250000000000 : ℝ)*(base19) + (5599089/625000000000 : ℝ)*(base23) + (27665071/100000000000000 : ℝ)*(upper3) + (195924567/100000000000000 : ℝ)*(upper4) + (39680563/20000000000000 : ℝ)*(upper5) + (1407958958171293/50000000000000 : ℝ)*(major0) + (1407958958171293/50000000000000 : ℝ)*(major1) + (1407958958171293/50000000000000 : ℝ)*(major2) + (979999501113543/25000000000000 : ℝ)*(sp0) + (1960008432656281/50000000000000 : ℝ)*(sp1) + (3920016685144259/100000000000000 : ℝ)*(sp2) + (427952442078159/25000000000000 : ℝ)*(sp3) + (19576544327/100000000000000 : ℝ)*(sp4) + (16823327/200000000000 : ℝ)*(sp7) + (213977272497017/12500000000000 : ℝ)*(f.failure) + (1960008790499249/50000000000000 : ℝ)*(f.sum) + (106696344697677/24110000000000000000000000000 : ℝ)*base66 + (7270382321720810991/1205500000000000000000000000000000 : ℝ)*base67 + (1816581179744810991/1205500000000000000000000000000000 : ℝ)*base69 + (10920306424620689009/1205500000000000000000000000000000 : ℝ)*base72 + (72444681285833/24110000000000000000000000000 : ℝ)*base73 + (8404171904117310991/1205500000000000000000000000000000 : ℝ)*base75 + (2496022173640310991/1205500000000000000000000000000000 : ℝ)*base77 + (10783384995649189009/1205500000000000000000000000000000 : ℝ)*base80 + (14093363678377/24110000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (8006169/1250000000000000000000 : ℝ)*base89 + (8006169/1250000000000000000000 : ℝ)*base91 + (8006169/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (816556893941917601195907/48220000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15911091/100000000000000 : ℝ)*(base19) + (892921849/100000000000000 : ℝ)*(base23) + (298022447/100000000000000 : ℝ)*(lower2) + (425986471/100000000000000 : ℝ)*(upper3) + (257914493/100000000000000 : ℝ)*(lower4) + (2851244604467511/100000000000000 : ℝ)*(major0) + (2851244604467511/100000000000000 : ℝ)*(major1) + (2851244604467511/100000000000000 : ℝ)*(major2) + (4964767269/20000000000000 : ℝ)*(sp2) + (7012027/500000000000 : ℝ)*(sp3) + (992298774703841/25000000000000 : ℝ)*(sp4) + (248074692681517/6250000000000 : ℝ)*(sp5) + (396916938205717/10000000000000 : ℝ)*(sp6) + (1733292143247991/100000000000000 : ℝ)*(sp7) + (108330846603337/6250000000000 : ℝ)*(f.failure) + (992298774703841/25000000000000 : ℝ)*(f.sum) + (69560346369751/48220000000000000000000000000 : ℝ)*base65 + (2192359090829597043/2411000000000000000000000000000000 : ℝ)*base68 + (10473254783835597043/2411000000000000000000000000000000 : ℝ)*base70 + (15329475907502402957/2411000000000000000000000000000000 : ℝ)*base71 + (29128849835111/48220000000000000000000000000 : ℝ)*base73 + (121941663984402957/2411000000000000000000000000000000 : ℝ)*base75 + (439552574262402957/2411000000000000000000000000000000 : ℝ)*base77 + (7494707908152597043/2411000000000000000000000000000000 : ℝ)*base80 + (22365740323829/48220000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4468409/625000000000000000000 : ℝ)*base89 + (4468409/625000000000000000000 : ℝ)*base91 + (4468409/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1526_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2273/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (427/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (659/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7973/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1526_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1526_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (659/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7973/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1526_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1526_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1526_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4547/1024 : ℝ) ≤ p) (hpb : p ≤ (4549/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164498657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (659/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7973/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1526_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
