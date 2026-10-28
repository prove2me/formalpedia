-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1291_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:22.449817+00:00
-- url     : https://prove2.me/submissions/e8367dc0-907c-46fd-9c19-2d8199c244dd

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
theorem support_rectangle_w1291_s6_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417770987/2000000000 : ℝ)*x 0 + (2707687629/5000000000 : ℝ)*x 1 + (5242869657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417770987/2000000000 : ℝ)^4251 ≤ (12708661557439/100000000000000 : ℝ)^3227 := by
    have hnat : (417770987 : ℕ)^4251*100000000000000^3227 ≤ 12708661557439^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417770987 2000000000 12708661557439 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707687629/5000000000 : ℝ)^4251 ≤ (44576183223897/100000000000000 : ℝ)^3227 := by
    have hnat : (2707687629 : ℕ)^4251*100000000000000^3227 ≤ 44576183223897^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707687629 5000000000 44576183223897 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242869657/10000000000 : ℝ)^4251 ≤ (2669697200553/6250000000000 : ℝ)^3227 := by
    have hnat : (5242869657 : ℕ)^4251*6250000000000^3227 ≤ 2669697200553^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242869657 10000000000 2669697200553 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417770987/2000000000 : ℝ), (2707687629/5000000000 : ℝ), (5242869657/10000000000 : ℝ)] ![(12708661557439/100000000000000 : ℝ), (44576183223897/100000000000000 : ℝ), (2669697200553/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417770987/2000000000 : ℝ)|^4251 ≤ (12708661557439/100000000000000 : ℝ)^3227
        have hw : |(-417770987/2000000000 : ℝ)|=(417770987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707687629/5000000000 : ℝ)|^4251 ≤ (44576183223897/100000000000000 : ℝ)^3227
        have hw : |(2707687629/5000000000 : ℝ)|=(2707687629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242869657/10000000000 : ℝ)|^4251 ≤ (2669697200553/6250000000000 : ℝ)^3227
        have hw : |(5242869657/10000000000 : ℝ)|=(5242869657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349822853/10000000000 : ℝ)*x 0 + (-2176791637/10000000000 : ℝ)*x 1 + (2621434829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349822853/10000000000 : ℝ)^4251 ≤ (350933916899/800000000000 : ℝ)^3227 := by
    have hnat : (5349822853 : ℕ)^4251*800000000000^3227 ≤ 350933916899^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349822853 10000000000 350933916899 800000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176791637/10000000000 : ℝ)^4251 ≤ (13418105150347/100000000000000 : ℝ)^3227 := by
    have hnat : (2176791637 : ℕ)^4251*100000000000000^3227 ≤ 13418105150347^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176791637 10000000000 13418105150347 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621434829/5000000000 : ℝ)^4251 ≤ (2135757760979/5000000000000 : ℝ)^3227 := by
    have hnat : (2621434829 : ℕ)^4251*5000000000000^3227 ≤ 2135757760979^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621434829 5000000000 2135757760979 5000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349822853/10000000000 : ℝ), (-2176791637/10000000000 : ℝ), (2621434829/5000000000 : ℝ)] ![(350933916899/800000000000 : ℝ), (13418105150347/100000000000000 : ℝ), (2135757760979/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349822853/10000000000 : ℝ)|^4251 ≤ (350933916899/800000000000 : ℝ)^3227
        have hw : |(5349822853/10000000000 : ℝ)|=(5349822853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176791637/10000000000 : ℝ)|^4251 ≤ (13418105150347/100000000000000 : ℝ)^3227
        have hw : |(-2176791637/10000000000 : ℝ)|=(2176791637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621434829/5000000000 : ℝ)|^4251 ≤ (2135757760979/5000000000000 : ℝ)^3227
        have hw : |(2621434829/5000000000 : ℝ)|=(2621434829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069964571/2000000000 : ℝ)*x 0 + (655358707/1250000000 : ℝ)*x 1 + (-1088395819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069964571/2000000000 : ℝ)^4251 ≤ (21933369816989/50000000000000 : ℝ)^3227 := by
    have hnat : (1069964571 : ℕ)^4251*50000000000000^3227 ≤ 21933369816989^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069964571 2000000000 21933369816989 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655358707/1250000000 : ℝ)^4251 ≤ (8543031039623/20000000000000 : ℝ)^3227 := by
    have hnat : (655358707 : ℕ)^4251*20000000000000^3227 ≤ 8543031039623^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655358707 1250000000 8543031039623 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088395819/5000000000 : ℝ)^4251 ≤ (13418105158467/100000000000000 : ℝ)^3227 := by
    have hnat : (1088395819 : ℕ)^4251*100000000000000^3227 ≤ 13418105158467^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088395819 5000000000 13418105158467 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069964571/2000000000 : ℝ), (655358707/1250000000 : ℝ), (-1088395819/5000000000 : ℝ)] ![(21933369816989/50000000000000 : ℝ), (8543031039623/20000000000000 : ℝ), (13418105158467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069964571/2000000000 : ℝ)|^4251 ≤ (21933369816989/50000000000000 : ℝ)^3227
        have hw : |(1069964571/2000000000 : ℝ)|=(1069964571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655358707/1250000000 : ℝ)|^4251 ≤ (8543031039623/20000000000000 : ℝ)^3227
        have hw : |(655358707/1250000000 : ℝ)|=(655358707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088395819/5000000000 : ℝ)|^4251 ≤ (13418105158467/100000000000000 : ℝ)^3227
        have hw : |(-1088395819/5000000000 : ℝ)|=(1088395819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86802581/200000000 : ℝ)*x 0 + (833277263/2000000000 : ℝ)*x 1 + (180831631/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86802581/200000000 : ℝ)^4251 ≤ (1665114286447/5000000000000 : ℝ)^3227 := by
    have hnat : (86802581 : ℕ)^4251*5000000000000^3227 ≤ 1665114286447^3227*200000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86802581 200000000 1665114286447 5000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833277263/2000000000 : ℝ)^4251 ≤ (6311471749691/20000000000000 : ℝ)^3227 := by
    have hnat : (833277263 : ℕ)^4251*20000000000000^3227 ≤ 6311471749691^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833277263 2000000000 6311471749691 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180831631/400000000 : ℝ)^4251 ≤ (35140355506829/100000000000000 : ℝ)^3227 := by
    have hnat : (180831631 : ℕ)^4251*100000000000000^3227 ≤ 35140355506829^3227*400000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180831631 400000000 35140355506829 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86802581/200000000 : ℝ), (833277263/2000000000 : ℝ), (180831631/400000000 : ℝ)] ![(1665114286447/5000000000000 : ℝ), (6311471749691/20000000000000 : ℝ), (35140355506829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86802581/200000000 : ℝ)|^4251 ≤ (1665114286447/5000000000000 : ℝ)^3227
        have hw : |(86802581/200000000 : ℝ)|=(86802581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833277263/2000000000 : ℝ)|^4251 ≤ (6311471749691/20000000000000 : ℝ)^3227
        have hw : |(833277263/2000000000 : ℝ)|=(833277263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180831631/400000000 : ℝ)|^4251 ≤ (35140355506829/100000000000000 : ℝ)^3227
        have hw : |(180831631/400000000 : ℝ)|=(180831631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417773479/2000000000 : ℝ)*x 0 + (1048697027/2000000000 : ℝ)*x 1 + (2707378419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417773479/2000000000 : ℝ)^4251 ≤ (3177190354967/25000000000000 : ℝ)^3227 := by
    have hnat : (417773479 : ℕ)^4251*25000000000000^3227 ≤ 3177190354967^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417773479 2000000000 3177190354967 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048697027/2000000000 : ℝ)^4251 ≤ (21360880506473/50000000000000 : ℝ)^3227 := by
    have hnat : (1048697027 : ℕ)^4251*50000000000000^3227 ≤ 21360880506473^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048697027 2000000000 21360880506473 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707378419/5000000000 : ℝ)^4251 ≤ (22284738777387/50000000000000 : ℝ)^3227 := by
    have hnat : (2707378419 : ℕ)^4251*50000000000000^3227 ≤ 22284738777387^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707378419 5000000000 22284738777387 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417773479/2000000000 : ℝ), (1048697027/2000000000 : ℝ), (2707378419/5000000000 : ℝ)] ![(3177190354967/25000000000000 : ℝ), (21360880506473/50000000000000 : ℝ), (22284738777387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417773479/2000000000 : ℝ)|^4251 ≤ (3177190354967/25000000000000 : ℝ)^3227
        have hw : |(-417773479/2000000000 : ℝ)|=(417773479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048697027/2000000000 : ℝ)|^4251 ≤ (21360880506473/50000000000000 : ℝ)^3227
        have hw : |(1048697027/2000000000 : ℝ)|=(1048697027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707378419/5000000000 : ℝ)|^4251 ≤ (22284738777387/50000000000000 : ℝ)^3227
        have hw : |(2707378419/5000000000 : ℝ)|=(2707378419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_5 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331603921/625000000 : ℝ)*x 0 + (-2004904417/10000000000 : ℝ)*x 1 + (5414756623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331603921/625000000 : ℝ)^4251 ≤ (43390365578063/100000000000000 : ℝ)^3227 := by
    have hnat : (331603921 : ℕ)^4251*100000000000000^3227 ≤ 43390365578063^3227*625000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331603921 625000000 43390365578063 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004904417/10000000000 : ℝ)^4251 ≤ (12040159184239/100000000000000 : ℝ)^3227 := by
    have hnat : (2004904417 : ℕ)^4251*100000000000000^3227 ≤ 12040159184239^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004904417 10000000000 12040159184239 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414756623/10000000000 : ℝ)^4251 ≤ (22284737611761/50000000000000 : ℝ)^3227 := by
    have hnat : (5414756623 : ℕ)^4251*50000000000000^3227 ≤ 22284737611761^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414756623 10000000000 22284737611761 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331603921/625000000 : ℝ), (-2004904417/10000000000 : ℝ), (5414756623/10000000000 : ℝ)] ![(43390365578063/100000000000000 : ℝ), (12040159184239/100000000000000 : ℝ), (22284737611761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331603921/625000000 : ℝ)|^4251 ≤ (43390365578063/100000000000000 : ℝ)^3227
        have hw : |(331603921/625000000 : ℝ)|=(331603921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004904417/10000000000 : ℝ)|^4251 ≤ (12040159184239/100000000000000 : ℝ)^3227
        have hw : |(-2004904417/10000000000 : ℝ)|=(2004904417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414756623/10000000000 : ℝ)|^4251 ≤ (22284737611761/50000000000000 : ℝ)^3227
        have hw : |(5414756623/10000000000 : ℝ)|=(5414756623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_6 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061132509/2000000000 : ℝ)*x 0 + (676844581/1250000000 : ℝ)*x 1 + (-1002452321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061132509/2000000000 : ℝ)^4251 ≤ (5423795440047/12500000000000 : ℝ)^3227 := by
    have hnat : (1061132509 : ℕ)^4251*12500000000000^3227 ≤ 5423795440047^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061132509 2000000000 5423795440047 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676844581/1250000000 : ℝ)^4251 ≤ (22284737747299/50000000000000 : ℝ)^3227 := by
    have hnat : (676844581 : ℕ)^4251*50000000000000^3227 ≤ 22284737747299^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676844581 1250000000 22284737747299 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002452321/5000000000 : ℝ)^4251 ≤ (12040160964211/100000000000000 : ℝ)^3227 := by
    have hnat : (1002452321 : ℕ)^4251*100000000000000^3227 ≤ 12040160964211^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002452321 5000000000 12040160964211 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061132509/2000000000 : ℝ), (676844581/1250000000 : ℝ), (-1002452321/5000000000 : ℝ)] ![(5423795440047/12500000000000 : ℝ), (22284737747299/50000000000000 : ℝ), (12040160964211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061132509/2000000000 : ℝ)|^4251 ≤ (5423795440047/12500000000000 : ℝ)^3227
        have hw : |(1061132509/2000000000 : ℝ)|=(1061132509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676844581/1250000000 : ℝ)|^4251 ≤ (22284737747299/50000000000000 : ℝ)^3227
        have hw : |(676844581/1250000000 : ℝ)|=(676844581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002452321/5000000000 : ℝ)|^4251 ≤ (12040160964211/100000000000000 : ℝ)^3227
        have hw : |(-1002452321/5000000000 : ℝ)|=(1002452321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s6_7 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340155111/10000000000 : ℝ)*x 0 + (4519526383/10000000000 : ℝ)*x 1 + (416765737/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340155111/10000000000 : ℝ)^4251 ≤ (2081409322047/6250000000000 : ℝ)^3227 := by
    have hnat : (4340155111 : ℕ)^4251*6250000000000^3227 ≤ 2081409322047^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340155111 10000000000 2081409322047 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519526383/10000000000 : ℝ)^4251 ≤ (35127409186509/100000000000000 : ℝ)^3227 := by
    have hnat : (4519526383 : ℕ)^4251*100000000000000^3227 ≤ 35127409186509^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519526383 10000000000 35127409186509 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416765737/1000000000 : ℝ)^4251 ≤ (31570041649769/100000000000000 : ℝ)^3227 := by
    have hnat : (416765737 : ℕ)^4251*100000000000000^3227 ≤ 31570041649769^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416765737 1000000000 31570041649769 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340155111/10000000000 : ℝ), (4519526383/10000000000 : ℝ), (416765737/1000000000 : ℝ)] ![(2081409322047/6250000000000 : ℝ), (35127409186509/100000000000000 : ℝ), (31570041649769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340155111/10000000000 : ℝ)|^4251 ≤ (2081409322047/6250000000000 : ℝ)^3227
        have hw : |(4340155111/10000000000 : ℝ)|=(4340155111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519526383/10000000000 : ℝ)|^4251 ≤ (35127409186509/100000000000000 : ℝ)^3227
        have hw : |(4519526383/10000000000 : ℝ)|=(4519526383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416765737/1000000000 : ℝ)|^4251 ≤ (31570041649769/100000000000000 : ℝ)^3227
        have hw : |(416765737/1000000000 : ℝ)|=(416765737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2753/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2753/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2753/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2753/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2753/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2753/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2753/25000 : ℝ) ^ (2125/512 : ℝ) ≤ (10552867136300913/100000000000000000000 : ℝ) := by
    have hpowers : (2753/25000 : ℝ)^2125 ≤ (10552867136300913/100000000000000000000 : ℝ)^512 := by
      have hnat : (2753 : ℕ)^2125*100000000000000000000^512 ≤ 10552867136300913^512*25000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2753 25000 10552867136300913 100000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2753/25000 : ℝ)) (X := (10552867136300913/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (2125/512 : ℝ) ≤ (8714936046271643/25000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^2125 ≤ (8714936046271643/25000000000000000000 : ℝ)^512 := by
      have hnat : (7343 : ℕ)^2125*25000000000000000000^512 ≤ 8714936046271643^512*50000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 8714936046271643 25000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (8714936046271643/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010552867136300913/50000000000000000000 : ℝ) ≤ (10000508483315601/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50010552867136300913/50000000000000000000 : ℝ)^512 ≤ (10000508483315601/10000000000000000 : ℝ)^2125 := by
      have hnat : (50010552867136300913 : ℕ)^512*10000000000000000^2125 ≤ 10000508483315601^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010552867136300913 50000000000000000000 10000508483315601 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000508483315601/10000000000000000 : ℝ)) (X := (50010552867136300913/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009082522264277497/20000000000000000000 : ℝ) ≤ (5000546994132027/5000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (20009082522264277497/20000000000000000000 : ℝ)^512 ≤ (5000546994132027/5000000000000000 : ℝ)^2125 := by
      have hnat : (20009082522264277497 : ℕ)^512*5000000000000000^2125 ≤ 5000546994132027^2125*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009082522264277497 20000000000000000000 5000546994132027 5000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546994132027/5000000000000000 : ℝ)) (X := (20009082522264277497/20000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508714936046271643/12500000000000000000 : ℝ) ≤ (10001679493212507/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (12508714936046271643/12500000000000000000 : ℝ)^512 ≤ (10001679493212507/10000000000000000 : ℝ)^2125 := by
      have hnat : (12508714936046271643 : ℕ)^512*10000000000000000^2125 ≤ 10001679493212507^2125*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508714936046271643 12500000000000000000 10001679493212507 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001679493212507/10000000000000000 : ℝ)) (X := (12508714936046271643/12500000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10552867136300913/100000000000000000000 : ℝ) ≤ ((18364486503358394601/18370000000000000000 : ℝ)+2*(585504948453/367400000000000 : ℝ)*(2753/25000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (18364486503358394601/18370000000000000000 : ℝ)+2*(585504948453/367400000000000 : ℝ)*(2753/25000 : ℝ)=(10000508483315601/10000000000000000 : ℝ) by norm_num, show 1+2*(10552867136300913/100000000000000000000 : ℝ)=(50010552867136300913/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8714936046271643/25000000000000000000 : ℝ)+(10552867136300913/100000000000000000000 : ℝ) ≤ ((18364486503358394601/18370000000000000000 : ℝ)+(585504948453/367400000000000 : ℝ)*((7343/50000 : ℝ)+(2753/25000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (18364486503358394601/18370000000000000000 : ℝ)+(585504948453/367400000000000 : ℝ)*((7343/50000 : ℝ)+(2753/25000 : ℝ))=(5000546994132027/5000000000000000 : ℝ) by norm_num, show 1+(8714936046271643/25000000000000000000 : ℝ)+(10552867136300913/100000000000000000000 : ℝ)=(20009082522264277497/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8714936046271643/25000000000000000000 : ℝ) ≤ ((18364486503358394601/18370000000000000000 : ℝ)+2*(585504948453/367400000000000 : ℝ)*(7343/50000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (18364486503358394601/18370000000000000000 : ℝ)+2*(585504948453/367400000000000 : ℝ)*(7343/50000 : ℝ)=(10001679493212507/10000000000000000 : ℝ) by norm_num, show 1+2*(8714936046271643/25000000000000000000 : ℝ)=(12508714936046271643/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18364486503358394601/18370000000000000000 : ℝ)*(X 1 0+X 2 0)+(585504948453/367400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (18364486503358394601/18370000000000000000 : ℝ)) (alpha := (585504948453/367400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18364486503358394601/18370000000000000000 : ℝ)*(X 0 1+X 2 1)+(585504948453/367400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (18364486503358394601/18370000000000000000 : ℝ)) (alpha := (585504948453/367400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18364486503358394601/18370000000000000000 : ℝ)*(X 0 2+X 1 2)+(585504948453/367400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (2753/25000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (18364486503358394601/18370000000000000000 : ℝ)) (alpha := (585504948453/367400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417770987/2000000000 : ℝ)*X 0 0+(2707687629/5000000000 : ℝ)*X 0 1+(5242869657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349822853/10000000000 : ℝ)*X 1 0+(-2176791637/10000000000 : ℝ)*X 1 1+(2621434829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069964571/2000000000 : ℝ)*X 2 0+(655358707/1250000000 : ℝ)*X 2 1+(-1088395819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86802581/200000000 : ℝ)*X 0 0+(833277263/2000000000 : ℝ)*X 0 1+(180831631/400000000 : ℝ)*X 0 2+(86802581/200000000 : ℝ)*X 1 0+(833277263/2000000000 : ℝ)*X 1 1+(180831631/400000000 : ℝ)*X 1 2+(86802581/200000000 : ℝ)*X 2 0+(833277263/2000000000 : ℝ)*X 2 1+(180831631/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-417773479/2000000000 : ℝ)*X 0 0+(1048697027/2000000000 : ℝ)*X 0 1+(2707378419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331603921/625000000 : ℝ)*X 1 0+(-2004904417/10000000000 : ℝ)*X 1 1+(5414756623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061132509/2000000000 : ℝ)*X 2 0+(676844581/1250000000 : ℝ)*X 2 1+(-1002452321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340155111/10000000000 : ℝ)*X 0 0+(4519526383/10000000000 : ℝ)*X 0 1+(416765737/1000000000 : ℝ)*X 0 2+(4340155111/10000000000 : ℝ)*X 1 0+(4519526383/10000000000 : ℝ)*X 1 1+(416765737/1000000000 : ℝ)*X 1 2+(4340155111/10000000000 : ℝ)*X 2 0+(4519526383/10000000000 : ℝ)*X 2 1+(416765737/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3037371886125522476854107489/459250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1266363891/100000000000000 : ℝ)*(base19) + (295513/25000000000 : ℝ)*(base23) + (46264761/100000000000000 : ℝ)*(lower2) + (653041/390625000000 : ℝ)*(upper3) + (51293481/50000000000000 : ℝ)*(upper5) + (2154656409429363/50000000000000 : ℝ)*(major0) + (2154656409429363/50000000000000 : ℝ)*(major1) + (2154656409429363/50000000000000 : ℝ)*(major2) + (9275103603419/160000000000 : ℝ)*(sp0) + (5796963841183921/100000000000000 : ℝ)*(sp1) + (1449240981373953/25000000000000 : ℝ)*(sp2) + (282164692260819/10000000000000 : ℝ)*(sp3) + (12677705469/50000000000000 : ℝ)*(sp4) + (1673387823/12500000000000 : ℝ)*(sp7) + (1410830154855387/50000000000000 : ℝ)*(f.failure) + (5796965107547813/100000000000000 : ℝ)*(f.sum) + (19967650719013/4592500000000000000000000000 : ℝ)*base66 + (7713666932024980837/918500000000000000000000000000000 : ℝ)*base68 + (12476868638744480837/918500000000000000000000000000000 : ℝ)*base70 + (6067654343172480837/918500000000000000000000000000000 : ℝ)*base72 + (4191004037943/4592500000000000000000000000 : ℝ)*base74 + (5411310969824019163/918500000000000000000000000000000 : ℝ)*base75 + (5243242403441980837/918500000000000000000000000000000 : ℝ)*base78 + (4441729652273019163/918500000000000000000000000000000 : ℝ)*base79 + (18051484026251/9185000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (48756939/2500000000000000000000 : ℝ)*base89 + (48756939/2500000000000000000000 : ℝ)*base91 + (48756939/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1855420732015038360056062473/229625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1211764157/100000000000000 : ℝ)*(base19) + (41167383/3125000000000 : ℝ)*(base23) + (1468157/781250000000 : ℝ)*(lower4) + (4256717/4000000000000 : ℝ)*(upper5) + (1085079807373891/25000000000000 : ℝ)*(major0) + (1085079807373891/25000000000000 : ℝ)*(major1) + (1085079807373891/25000000000000 : ℝ)*(major2) + (713923433/100000000000000 : ℝ)*(sp0) + (3216963427/12500000000000 : ℝ)*(sp1) + (21120180479/100000000000000 : ℝ)*(sp2) + (2919337363786139/50000000000000 : ℝ)*(sp4) + (2919324247012069/50000000000000 : ℝ)*(sp5) + (91228953186859/1562500000000 : ℝ)*(sp6) + (2841962748154713/100000000000000 : ℝ)*(sp7) + (2841962748154713/100000000000000 : ℝ)*(f.failure) + (5838675441495711/100000000000000 : ℝ)*(f.sum) + (2717177844037/287031250000000000000000000 : ℝ)*base66 + (2268278389966162491/459250000000000000000000000000000 : ℝ)*base67 + (1248011914054837509/459250000000000000000000000000000 : ℝ)*base70 + (4106197138916837509/459250000000000000000000000000000 : ℝ)*base72 + (31558400962839/9185000000000000000000000000 : ℝ)*base74 + (2135576952082087509/459250000000000000000000000000000 : ℝ)*base76 + (5965839104920087509/459250000000000000000000000000000 : ℝ)*base78 + (2864288710157162491/459250000000000000000000000000000 : ℝ)*base79 + (1323783534143/4592500000000000000000000000 : ℝ)*base81 + (41342761/5000000000000000000000 : ℝ)*base89 + (41342761/5000000000000000000000 : ℝ)*base91 + (41342761/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1291_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1291_s7_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2088867737/10000000000 : ℝ)*x 0 + (5415270609/10000000000 : ℝ)*x 1 + (209718633/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088867737/10000000000 : ℝ)^4251 ≤ (6354382080439/50000000000000 : ℝ)^3227 := by
    have hnat : (2088867737 : ℕ)^4251*50000000000000^3227 ≤ 6354382080439^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088867737 10000000000 6354382080439 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415270609/10000000000 : ℝ)^4251 ≤ (22287524236919/50000000000000 : ℝ)^3227 := by
    have hnat : (5415270609 : ℕ)^4251*50000000000000^3227 ≤ 22287524236919^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415270609 10000000000 22287524236919 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209718633/400000000 : ℝ)^4251 ≤ (21358093672411/50000000000000 : ℝ)^3227 := by
    have hnat : (209718633 : ℕ)^4251*50000000000000^3227 ≤ 21358093672411^3227*400000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209718633 400000000 21358093672411 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2088867737/10000000000 : ℝ), (5415270609/10000000000 : ℝ), (209718633/400000000 : ℝ)] ![(6354382080439/50000000000000 : ℝ), (22287524236919/50000000000000 : ℝ), (21358093672411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2088867737/10000000000 : ℝ)|^4251 ≤ (6354382080439/50000000000000 : ℝ)^3227
        have hw : |(-2088867737/10000000000 : ℝ)|=(2088867737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415270609/10000000000 : ℝ)|^4251 ≤ (22287524236919/50000000000000 : ℝ)^3227
        have hw : |(5415270609/10000000000 : ℝ)|=(5415270609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209718633/400000000 : ℝ)|^4251 ≤ (21358093672411/50000000000000 : ℝ)^3227
        have hw : |(209718633/400000000 : ℝ)|=(209718633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674897757/5000000000 : ℝ)*x 0 + (-544175019/2500000000 : ℝ)*x 1 + (5242966447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674897757/5000000000 : ℝ)^4251 ≤ (43866444307669/100000000000000 : ℝ)^3227 := by
    have hnat : (2674897757 : ℕ)^4251*100000000000000^3227 ≤ 43866444307669^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674897757 5000000000 43866444307669 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544175019/2500000000 : ℝ)^4251 ≤ (2683472332423/20000000000000 : ℝ)^3227 := by
    have hnat : (544175019 : ℕ)^4251*20000000000000^3227 ≤ 2683472332423^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544175019 2500000000 2683472332423 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242966447/10000000000 : ℝ)^4251 ≤ (2135809701027/5000000000000 : ℝ)^3227 := by
    have hnat : (5242966447 : ℕ)^4251*5000000000000^3227 ≤ 2135809701027^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242966447 10000000000 2135809701027 5000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674897757/5000000000 : ℝ), (-544175019/2500000000 : ℝ), (5242966447/10000000000 : ℝ)] ![(43866444307669/100000000000000 : ℝ), (2683472332423/20000000000000 : ℝ), (2135809701027/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674897757/5000000000 : ℝ)|^4251 ≤ (43866444307669/100000000000000 : ℝ)^3227
        have hw : |(2674897757/5000000000 : ℝ)|=(2674897757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544175019/2500000000 : ℝ)|^4251 ≤ (2683472332423/20000000000000 : ℝ)^3227
        have hw : |(-544175019/2500000000 : ℝ)|=(544175019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242966447/10000000000 : ℝ)|^4251 ≤ (2135809701027/5000000000000 : ℝ)^3227
        have hw : |(5242966447/10000000000 : ℝ)|=(5242966447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349795887/10000000000 : ℝ)*x 0 + (2621482273/5000000000 : ℝ)*x 1 + (-544175523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349795887/10000000000 : ℝ)^4251 ≤ (43866448336659/100000000000000 : ℝ)^3227 := by
    have hnat : (5349795887 : ℕ)^4251*100000000000000^3227 ≤ 43866448336659^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349795887 10000000000 43866448336659 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621482273/5000000000 : ℝ)^4251 ≤ (2669760851109/6250000000000 : ℝ)^3227 := by
    have hnat : (2621482273 : ℕ)^4251*6250000000000^3227 ≤ 2669760851109^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621482273 5000000000 2669760851109 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544175523/2500000000 : ℝ)^4251 ≤ (3354344508053/25000000000000 : ℝ)^3227 := by
    have hnat : (544175523 : ℕ)^4251*25000000000000^3227 ≤ 3354344508053^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544175523 2500000000 3354344508053 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349795887/10000000000 : ℝ), (2621482273/5000000000 : ℝ), (-544175523/2500000000 : ℝ)] ![(43866448336659/100000000000000 : ℝ), (2669760851109/6250000000000 : ℝ), (3354344508053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349795887/10000000000 : ℝ)|^4251 ≤ (43866448336659/100000000000000 : ℝ)^3227
        have hw : |(5349795887/10000000000 : ℝ)|=(5349795887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621482273/5000000000 : ℝ)|^4251 ≤ (2669760851109/6250000000000 : ℝ)^3227
        have hw : |(2621482273/5000000000 : ℝ)|=(2621482273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544175523/2500000000 : ℝ)|^4251 ≤ (3354344508053/25000000000000 : ℝ)^3227
        have hw : |(-544175523/2500000000 : ℝ)|=(544175523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340134391/10000000000 : ℝ)*x 0 + (4166592541/10000000000 : ℝ)*x 1 + (4520584547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340134391/10000000000 : ℝ)^4251 ≤ (2081396232223/6250000000000 : ℝ)^3227 := by
    have hnat : (4340134391 : ℕ)^4251*6250000000000^3227 ≤ 2081396232223^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340134391 10000000000 2081396232223 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166592541/10000000000 : ℝ)^4251 ≤ (15779708219541/50000000000000 : ℝ)^3227 := by
    have hnat : (4166592541 : ℕ)^4251*50000000000000^3227 ≤ 15779708219541^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166592541 10000000000 15779708219541 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520584547/10000000000 : ℝ)^4251 ≤ (35138243825553/100000000000000 : ℝ)^3227 := by
    have hnat : (4520584547 : ℕ)^4251*100000000000000^3227 ≤ 35138243825553^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520584547 10000000000 35138243825553 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340134391/10000000000 : ℝ), (4166592541/10000000000 : ℝ), (4520584547/10000000000 : ℝ)] ![(2081396232223/6250000000000 : ℝ), (15779708219541/50000000000000 : ℝ), (35138243825553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340134391/10000000000 : ℝ)|^4251 ≤ (2081396232223/6250000000000 : ℝ)^3227
        have hw : |(4340134391/10000000000 : ℝ)|=(4340134391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166592541/10000000000 : ℝ)|^4251 ≤ (15779708219541/50000000000000 : ℝ)^3227
        have hw : |(4166592541/10000000000 : ℝ)|=(4166592541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520584547/10000000000 : ℝ)|^4251 ≤ (35138243825553/100000000000000 : ℝ)^3227
        have hw : |(4520584547/10000000000 : ℝ)|=(4520584547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208888061/1000000000 : ℝ)*x 0 + (2621789777/5000000000 : ℝ)*x 1 + (676831701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208888061/1000000000 : ℝ)^4251 ≤ (6354433666779/50000000000000 : ℝ)^3227 := by
    have hnat : (208888061 : ℕ)^4251*50000000000000^3227 ≤ 6354433666779^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208888061 1000000000 6354433666779 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621789777/5000000000 : ℝ)^4251 ≤ (42722774415237/100000000000000 : ℝ)^3227 := by
    have hnat : (2621789777 : ℕ)^4251*100000000000000^3227 ≤ 42722774415237^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621789777 5000000000 42722774415237 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676831701/1250000000 : ℝ)^4251 ≤ (8913671646401/20000000000000 : ℝ)^3227 := by
    have hnat : (676831701 : ℕ)^4251*20000000000000^3227 ≤ 8913671646401^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676831701 1250000000 8913671646401 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208888061/1000000000 : ℝ), (2621789777/5000000000 : ℝ), (676831701/1250000000 : ℝ)] ![(6354433666779/50000000000000 : ℝ), (42722774415237/100000000000000 : ℝ), (8913671646401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208888061/1000000000 : ℝ)|^4251 ≤ (6354433666779/50000000000000 : ℝ)^3227
        have hw : |(-208888061/1000000000 : ℝ)|=(208888061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621789777/5000000000 : ℝ)|^4251 ≤ (42722774415237/100000000000000 : ℝ)^3227
        have hw : |(2621789777/5000000000 : ℝ)|=(2621789777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676831701/1250000000 : ℝ)|^4251 ≤ (8913671646401/20000000000000 : ℝ)^3227
        have hw : |(676831701/1250000000 : ℝ)|=(676831701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_5 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305687113/10000000000 : ℝ)*x 0 + (-2005012573/10000000000 : ℝ)*x 1 + (1353663373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305687113/10000000000 : ℝ)^4251 ≤ (5423828524651/12500000000000 : ℝ)^3227 := by
    have hnat : (5305687113 : ℕ)^4251*12500000000000^3227 ≤ 5423828524651^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305687113 10000000000 5423828524651 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005012573/10000000000 : ℝ)^4251 ≤ (12041014812321/100000000000000 : ℝ)^3227 := by
    have hnat : (2005012573 : ℕ)^4251*100000000000000^3227 ≤ 12041014812321^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005012573 10000000000 12041014812321 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353663373/2500000000 : ℝ)^4251 ≤ (44568356974221/100000000000000 : ℝ)^3227 := by
    have hnat : (1353663373 : ℕ)^4251*100000000000000^3227 ≤ 44568356974221^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353663373 2500000000 44568356974221 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305687113/10000000000 : ℝ), (-2005012573/10000000000 : ℝ), (1353663373/2500000000 : ℝ)] ![(5423828524651/12500000000000 : ℝ), (12041014812321/100000000000000 : ℝ), (44568356974221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305687113/10000000000 : ℝ)|^4251 ≤ (5423828524651/12500000000000 : ℝ)^3227
        have hw : |(5305687113/10000000000 : ℝ)|=(5305687113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005012573/10000000000 : ℝ)|^4251 ≤ (12041014812321/100000000000000 : ℝ)^3227
        have hw : |(-2005012573/10000000000 : ℝ)|=(2005012573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353663373/2500000000 : ℝ)|^4251 ≤ (44568356974221/100000000000000 : ℝ)^3227
        have hw : |(1353663373/2500000000 : ℝ)|=(1353663373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_6 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652843577/5000000000 : ℝ)*x 0 + (5414653523/10000000000 : ℝ)*x 1 + (-80200499/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652843577/5000000000 : ℝ)^4251 ≤ (4339062863891/10000000000000 : ℝ)^3227 := by
    have hnat : (2652843577 : ℕ)^4251*10000000000000^3227 ≤ 4339062863891^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652843577 5000000000 4339062863891 10000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414653523/10000000000 : ℝ)^4251 ≤ (44568357310353/100000000000000 : ℝ)^3227 := by
    have hnat : (5414653523 : ℕ)^4251*100000000000000^3227 ≤ 44568357310353^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414653523 10000000000 44568357310353 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80200499/400000000 : ℝ)^4251 ≤ (12041014037031/100000000000000 : ℝ)^3227 := by
    have hnat : (80200499 : ℕ)^4251*100000000000000^3227 ≤ 12041014037031^3227*400000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80200499 400000000 12041014037031 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652843577/5000000000 : ℝ), (5414653523/10000000000 : ℝ), (-80200499/400000000 : ℝ)] ![(4339062863891/10000000000000 : ℝ), (44568357310353/100000000000000 : ℝ), (12041014037031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652843577/5000000000 : ℝ)|^4251 ≤ (4339062863891/10000000000000 : ℝ)^3227
        have hw : |(2652843577/5000000000 : ℝ)|=(2652843577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414653523/10000000000 : ℝ)|^4251 ≤ (44568357310353/100000000000000 : ℝ)^3227
        have hw : |(5414653523/10000000000 : ℝ)|=(5414653523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80200499/400000000 : ℝ)|^4251 ≤ (12041014037031/100000000000000 : ℝ)^3227
        have hw : |(-80200499/400000000 : ℝ)|=(80200499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s7_7 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868032439/2000000000 : ℝ)*x 0 + (2259661419/5000000000 : ℝ)*x 1 + (2083929519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868032439/2000000000 : ℝ)^4251 ≤ (33302620757699/100000000000000 : ℝ)^3227 := by
    have hnat : (868032439 : ℕ)^4251*100000000000000^3227 ≤ 33302620757699^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868032439 2000000000 33302620757699 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259661419/5000000000 : ℝ)^4251 ≤ (35125325162737/100000000000000 : ℝ)^3227 := by
    have hnat : (2259661419 : ℕ)^4251*100000000000000^3227 ≤ 35125325162737^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259661419 5000000000 35125325162737 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083929519/5000000000 : ℝ)^4251 ≤ (3157205405581/10000000000000 : ℝ)^3227 := by
    have hnat : (2083929519 : ℕ)^4251*10000000000000^3227 ≤ 3157205405581^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083929519 5000000000 3157205405581 10000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868032439/2000000000 : ℝ), (2259661419/5000000000 : ℝ), (2083929519/5000000000 : ℝ)] ![(33302620757699/100000000000000 : ℝ), (35125325162737/100000000000000 : ℝ), (3157205405581/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868032439/2000000000 : ℝ)|^4251 ≤ (33302620757699/100000000000000 : ℝ)^3227
        have hw : |(868032439/2000000000 : ℝ)|=(868032439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259661419/5000000000 : ℝ)|^4251 ≤ (35125325162737/100000000000000 : ℝ)^3227
        have hw : |(2259661419/5000000000 : ℝ)|=(2259661419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083929519/5000000000 : ℝ)|^4251 ≤ (3157205405581/10000000000000 : ℝ)^3227
        have hw : |(2083929519/5000000000 : ℝ)|=(2083929519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (441/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (917/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11023/100000 : ℝ) ^ (2125/512 : ℝ) ≤ (5298343409621261/50000000000000000000 : ℝ) := by
    have hpowers : (11023/100000 : ℝ)^2125 ≤ (5298343409621261/50000000000000000000 : ℝ)^512 := by
      have hnat : (11023 : ℕ)^2125*50000000000000000000^512 ≤ 5298343409621261^512*100000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11023 100000 5298343409621261 50000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11023/100000 : ℝ)) (X := (5298343409621261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (2125/512 : ℝ) ≤ (17370838137101659/50000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^2125 ≤ (17370838137101659/50000000000000000000 : ℝ)^512 := by
      have hnat : (7337 : ℕ)^2125*50000000000000000000^512 ≤ 17370838137101659^512*50000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 17370838137101659 50000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (17370838137101659/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005298343409621261/25000000000000000000 : ℝ) ≤ (5000255297284933/5000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (25005298343409621261/25000000000000000000 : ℝ)^512 ≤ (5000255297284933/5000000000000000 : ℝ)^2125 := by
      have hnat : (25005298343409621261 : ℕ)^512*5000000000000000^2125 ≤ 5000255297284933^2125*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005298343409621261 25000000000000000000 5000255297284933 5000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000255297284933/5000000000000000 : ℝ)) (X := (25005298343409621261/25000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250566729538668073/1250000000000000000 : ℝ) ≤ (10001092199934429/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (1250566729538668073/1250000000000000000 : ℝ)^512 ≤ (10001092199934429/10000000000000000 : ℝ)^2125 := by
      have hnat : (1250566729538668073 : ℕ)^512*10000000000000000^2125 ≤ 10001092199934429^2125*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250566729538668073 1250000000000000000 10001092199934429 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001092199934429/10000000000000000 : ℝ)) (X := (1250566729538668073/1250000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017370838137101659/25000000000000000000 : ℝ) ≤ (625104612831187/625000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (25017370838137101659/25000000000000000000 : ℝ)^512 ≤ (625104612831187/625000000000000 : ℝ)^2125 := by
      have hnat : (25017370838137101659 : ℕ)^512*625000000000000^2125 ≤ 625104612831187^2125*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017370838137101659 25000000000000000000 625104612831187 625000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625104612831187/625000000000000 : ℝ)) (X := (25017370838137101659/25000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5298343409621261/50000000000000000000 : ℝ) ≤ ((9124760527226856217/9127500000000000000 : ℝ)+2*(581605364563/365100000000000 : ℝ)*(11023/100000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (9124760527226856217/9127500000000000000 : ℝ)+2*(581605364563/365100000000000 : ℝ)*(11023/100000 : ℝ)=(5000255297284933/5000000000000000 : ℝ) by norm_num, show 1+2*(5298343409621261/50000000000000000000 : ℝ)=(25005298343409621261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17370838137101659/50000000000000000000 : ℝ)+(5298343409621261/50000000000000000000 : ℝ) ≤ ((9124760527226856217/9127500000000000000 : ℝ)+(581605364563/365100000000000 : ℝ)*((7337/50000 : ℝ)+(11023/100000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (9124760527226856217/9127500000000000000 : ℝ)+(581605364563/365100000000000 : ℝ)*((7337/50000 : ℝ)+(11023/100000 : ℝ))=(10001092199934429/10000000000000000 : ℝ) by norm_num, show 1+(17370838137101659/50000000000000000000 : ℝ)+(5298343409621261/50000000000000000000 : ℝ)=(1250566729538668073/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17370838137101659/50000000000000000000 : ℝ) ≤ ((9124760527226856217/9127500000000000000 : ℝ)+2*(581605364563/365100000000000 : ℝ)*(7337/50000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (9124760527226856217/9127500000000000000 : ℝ)+2*(581605364563/365100000000000 : ℝ)*(7337/50000 : ℝ)=(625104612831187/625000000000000 : ℝ) by norm_num, show 1+2*(17370838137101659/50000000000000000000 : ℝ)=(25017370838137101659/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9124760527226856217/9127500000000000000 : ℝ)*(X 1 0+X 2 0)+(581605364563/365100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9124760527226856217/9127500000000000000 : ℝ)) (alpha := (581605364563/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9124760527226856217/9127500000000000000 : ℝ)*(X 0 1+X 2 1)+(581605364563/365100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9124760527226856217/9127500000000000000 : ℝ)) (alpha := (581605364563/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9124760527226856217/9127500000000000000 : ℝ)*(X 0 2+X 1 2)+(581605364563/365100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9124760527226856217/9127500000000000000 : ℝ)) (alpha := (581605364563/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2088867737/10000000000 : ℝ)*X 0 0+(5415270609/10000000000 : ℝ)*X 0 1+(209718633/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674897757/5000000000 : ℝ)*X 1 0+(-544175019/2500000000 : ℝ)*X 1 1+(5242966447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349795887/10000000000 : ℝ)*X 2 0+(2621482273/5000000000 : ℝ)*X 2 1+(-544175523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340134391/10000000000 : ℝ)*X 0 0+(4166592541/10000000000 : ℝ)*X 0 1+(4520584547/10000000000 : ℝ)*X 0 2+(4340134391/10000000000 : ℝ)*X 1 0+(4166592541/10000000000 : ℝ)*X 1 1+(4520584547/10000000000 : ℝ)*X 1 2+(4340134391/10000000000 : ℝ)*X 2 0+(4166592541/10000000000 : ℝ)*X 2 1+(4520584547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208888061/1000000000 : ℝ)*X 0 0+(2621789777/5000000000 : ℝ)*X 0 1+(676831701/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305687113/10000000000 : ℝ)*X 1 0+(-2005012573/10000000000 : ℝ)*X 1 1+(1353663373/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652843577/5000000000 : ℝ)*X 2 0+(5414653523/10000000000 : ℝ)*X 2 1+(-80200499/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868032439/2000000000 : ℝ)*X 0 0+(2259661419/5000000000 : ℝ)*X 0 1+(2083929519/5000000000 : ℝ)*X 0 2+(868032439/2000000000 : ℝ)*X 1 0+(2259661419/5000000000 : ℝ)*X 1 1+(2083929519/5000000000 : ℝ)*X 1 2+(868032439/2000000000 : ℝ)*X 2 0+(2259661419/5000000000 : ℝ)*X 2 1+(2083929519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172806442218805260721353909/15212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26907231/12500000000000 : ℝ)*(base15) + (228952119/100000000000000 : ℝ)*(upper2) + (77790449/100000000000000 : ℝ)*(upper4) + (82456169/50000000000000 : ℝ)*(lower5) + (431432744578559/10000000000000 : ℝ)*(major0) + (431432744578559/10000000000000 : ℝ)*(major1) + (431432744578559/10000000000000 : ℝ)*(major2) + (1160739252687959/20000000000000 : ℝ)*(sp0) + (580371050068607/10000000000000 : ℝ)*(sp1) + (5803650061111423/100000000000000 : ℝ)*(sp2) + (353116660644553/12500000000000 : ℝ)*(sp3) + (14452504123/100000000000000 : ℝ)*(sp4) + (12130966499/20000000000000 : ℝ)*(sp6) + (5255910361/50000000000000 : ℝ)*(sp7) + (1412471898488573/50000000000000 : ℝ)*(f.failure) + (2901855357971959/50000000000000 : ℝ)*(f.sum) + (16157535634009/730200000000000000000000000 : ℝ)*base66 + (1212541709872198697/91275000000000000000000000000000 : ℝ)*base68 + (410866841002348697/91275000000000000000000000000000 : ℝ)*base70 + (2834224985094373697/91275000000000000000000000000000 : ℝ)*base72 + (1273205173333/1825500000000000000000000000 : ℝ)*base74 + (330860801371873697/91275000000000000000000000000000 : ℝ)*base76 + (547703763659398697/91275000000000000000000000000000 : ℝ)*base78 + (628678586008348697/91275000000000000000000000000000 : ℝ)*base80 + (736435212839/3651000000000000000000000000 : ℝ)*base82 + (23959181/2500000000000000000000 : ℝ)*base89 + (23959181/2500000000000000000000 : ℝ)*base91 + (23959181/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357575599115723158556305073/38031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49908487/3125000000000 : ℝ)*(base19) + (458765237/25000000000000 : ℝ)*(base23) + (227123137/50000000000000 : ℝ)*(lower1) + (26282481/12500000000000 : ℝ)*(upper3) + (7869617/12500000000000 : ℝ)*(lower4) + (14416587/12500000000000 : ℝ)*(upper5) + (2172655785602119/50000000000000 : ℝ)*(major0) + (2172655785602119/50000000000000 : ℝ)*(major1) + (2172655785602119/50000000000000 : ℝ)*(major2) + (8920383059/100000000000000 : ℝ)*(sp2) + (2922695592770619/50000000000000 : ℝ)*(sp4) + (2922694794234827/50000000000000 : ℝ)*(sp5) + (5845380430097231/100000000000000 : ℝ)*(sp6) + (1422615821731079/50000000000000 : ℝ)*(sp7) + (1422615821731079/50000000000000 : ℝ)*(f.failure) + (2922695592770619/50000000000000 : ℝ)*(f.sum) + (8971413092207/2281875000000000000000000000 : ℝ)*base66 + (2230975462823551177/456375000000000000000000000000000 : ℝ)*base68 + (4038018951355051177/456375000000000000000000000000000 : ℝ)*base70 + (5787225938694448823/456375000000000000000000000000000 : ℝ)*base71 + (1836726890213/570468750000000000000000000 : ℝ)*base74 + (10061094217438051177/456375000000000000000000000000000 : ℝ)*base76 + (1684080061087426177/456375000000000000000000000000000 : ℝ)*base78 + (5034064108064176177/456375000000000000000000000000000 : ℝ)*base80 + (9623001002011/18255000000000000000000000000 : ℝ)*base82 + (27649463/2500000000000000000000 : ℝ)*base89 + (27649463/2500000000000000000000 : ℝ)*base91 + (27649463/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1291_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (917/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1291_s8_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069958327/2000000000 : ℝ)*x 0 + (1048596451/2000000000 : ℝ)*x 1 + (-1088342171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069958327/2000000000 : ℝ)^4251 ≤ (8773280481667/20000000000000 : ℝ)^3227 := by
    have hnat : (1069958327 : ℕ)^4251*20000000000000^3227 ≤ 8773280481667^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069958327 2000000000 8773280481667 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048596451/2000000000 : ℝ)^4251 ≤ (8543272736521/20000000000000 : ℝ)^3227 := by
    have hnat : (1048596451 : ℕ)^4251*20000000000000^3227 ≤ 8543272736521^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048596451 2000000000 8543272736521 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088342171/5000000000 : ℝ)^4251 ≤ (2683446780163/20000000000000 : ℝ)^3227 := by
    have hnat : (1088342171 : ℕ)^4251*20000000000000^3227 ≤ 2683446780163^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088342171 5000000000 2683446780163 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069958327/2000000000 : ℝ), (1048596451/2000000000 : ℝ), (-1088342171/5000000000 : ℝ)] ![(8773280481667/20000000000000 : ℝ), (8543272736521/20000000000000 : ℝ), (2683446780163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069958327/2000000000 : ℝ)|^4251 ≤ (8773280481667/20000000000000 : ℝ)^3227
        have hw : |(1069958327/2000000000 : ℝ)|=(1069958327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048596451/2000000000 : ℝ)|^4251 ≤ (8543272736521/20000000000000 : ℝ)^3227
        have hw : |(1048596451/2000000000 : ℝ)|=(1048596451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088342171/5000000000 : ℝ)|^4251 ≤ (2683446780163/20000000000000 : ℝ)^3227
        have hw : |(-1088342171/5000000000 : ℝ)|=(1088342171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s8_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-522220601/2500000000 : ℝ)*x 0 + (2621798003/5000000000 : ℝ)*x 1 + (1353658999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522220601/2500000000 : ℝ)^4251 ≤ (12708881711869/100000000000000 : ℝ)^3227 := by
    have hnat : (522220601 : ℕ)^4251*100000000000000^3227 ≤ 12708881711869^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522220601 2500000000 12708881711869 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621798003/5000000000 : ℝ)^4251 ≤ (42722950995697/100000000000000 : ℝ)^3227 := by
    have hnat : (2621798003 : ℕ)^4251*100000000000000^3227 ≤ 42722950995697^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621798003 5000000000 42722950995697 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353658999/2500000000 : ℝ)^4251 ≤ (22284083632893/50000000000000 : ℝ)^3227 := by
    have hnat : (1353658999 : ℕ)^4251*50000000000000^3227 ≤ 22284083632893^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353658999 2500000000 22284083632893 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522220601/2500000000 : ℝ), (2621798003/5000000000 : ℝ), (1353658999/2500000000 : ℝ)] ![(12708881711869/100000000000000 : ℝ), (42722950995697/100000000000000 : ℝ), (22284083632893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522220601/2500000000 : ℝ)|^4251 ≤ (12708881711869/100000000000000 : ℝ)^3227
        have hw : |(-522220601/2500000000 : ℝ)|=(522220601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621798003/5000000000 : ℝ)|^4251 ≤ (42722950995697/100000000000000 : ℝ)^3227
        have hw : |(2621798003/5000000000 : ℝ)|=(2621798003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353658999/2500000000 : ℝ)|^4251 ≤ (22284083632893/50000000000000 : ℝ)^3227
        have hw : |(1353658999/2500000000 : ℝ)|=(1353658999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s8_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845743/5000000000 : ℝ)*x 0 + (-10025153/50000000 : ℝ)*x 1 + (1082927199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845743/5000000000 : ℝ)^4251 ≤ (10847668827151/25000000000000 : ℝ)^3227 := by
    have hnat : (2652845743 : ℕ)^4251*25000000000000^3227 ≤ 10847668827151^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845743 5000000000 10847668827151 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10025153/50000000 : ℝ)^4251 ≤ (12041157426337/100000000000000 : ℝ)^3227 := by
    have hnat : (10025153 : ℕ)^4251*100000000000000^3227 ≤ 12041157426337^3227*50000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10025153 50000000 12041157426337 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082927199/2000000000 : ℝ)^4251 ≤ (44568167254943/100000000000000 : ℝ)^3227 := by
    have hnat : (1082927199 : ℕ)^4251*100000000000000^3227 ≤ 44568167254943^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082927199 2000000000 44568167254943 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845743/5000000000 : ℝ), (-10025153/50000000 : ℝ), (1082927199/2000000000 : ℝ)] ![(10847668827151/25000000000000 : ℝ), (12041157426337/100000000000000 : ℝ), (44568167254943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845743/5000000000 : ℝ)|^4251 ≤ (10847668827151/25000000000000 : ℝ)^3227
        have hw : |(2652845743/5000000000 : ℝ)|=(2652845743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10025153/50000000 : ℝ)|^4251 ≤ (12041157426337/100000000000000 : ℝ)^3227
        have hw : |(-10025153/50000000 : ℝ)|=(10025153/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082927199/2000000000 : ℝ)|^4251 ≤ (44568167254943/100000000000000 : ℝ)^3227
        have hw : |(1082927199/2000000000 : ℝ)|=(1082927199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s8_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845743/5000000000 : ℝ)*x 0 + (1082927199/2000000000 : ℝ)*x 1 + (-10025153/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845743/5000000000 : ℝ)^4251 ≤ (10847668827151/25000000000000 : ℝ)^3227 := by
    have hnat : (2652845743 : ℕ)^4251*25000000000000^3227 ≤ 10847668827151^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845743 5000000000 10847668827151 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082927199/2000000000 : ℝ)^4251 ≤ (44568167254943/100000000000000 : ℝ)^3227 := by
    have hnat : (1082927199 : ℕ)^4251*100000000000000^3227 ≤ 44568167254943^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082927199 2000000000 44568167254943 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10025153/50000000 : ℝ)^4251 ≤ (12041157426337/100000000000000 : ℝ)^3227 := by
    have hnat : (10025153 : ℕ)^4251*100000000000000^3227 ≤ 12041157426337^3227*50000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10025153 50000000 12041157426337 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845743/5000000000 : ℝ), (1082927199/2000000000 : ℝ), (-10025153/50000000 : ℝ)] ![(10847668827151/25000000000000 : ℝ), (44568167254943/100000000000000 : ℝ), (12041157426337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845743/5000000000 : ℝ)|^4251 ≤ (10847668827151/25000000000000 : ℝ)^3227
        have hw : |(2652845743/5000000000 : ℝ)|=(2652845743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082927199/2000000000 : ℝ)|^4251 ≤ (44568167254943/100000000000000 : ℝ)^3227
        have hw : |(1082927199/2000000000 : ℝ)|=(1082927199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10025153/50000000 : ℝ)|^4251 ≤ (12041157426337/100000000000000 : ℝ)^3227
        have hw : |(-10025153/50000000 : ℝ)|=(10025153/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s8_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170081757/5000000000 : ℝ)*x 0 + (2259643723/5000000000 : ℝ)*x 1 + (4070209/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170081757/5000000000 : ℝ)^4251 ≤ (8325658522533/25000000000000 : ℝ)^3227 := by
    have hnat : (2170081757 : ℕ)^4251*25000000000000^3227 ≤ 8325658522533^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170081757 5000000000 8325658522533 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259643723/5000000000 : ℝ)^4251 ≤ (17562481399933/50000000000000 : ℝ)^3227 := by
    have hnat : (2259643723 : ℕ)^4251*50000000000000^3227 ≤ 17562481399933^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259643723 5000000000 17562481399933 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4070209/9765625 : ℝ)^4251 ≤ (493318798401/1562500000000 : ℝ)^3227 := by
    have hnat : (4070209 : ℕ)^4251*1562500000000^3227 ≤ 493318798401^3227*9765625^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4070209 9765625 493318798401 1562500000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170081757/5000000000 : ℝ), (2259643723/5000000000 : ℝ), (4070209/9765625 : ℝ)] ![(8325658522533/25000000000000 : ℝ), (17562481399933/50000000000000 : ℝ), (493318798401/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170081757/5000000000 : ℝ)|^4251 ≤ (8325658522533/25000000000000 : ℝ)^3227
        have hw : |(2170081757/5000000000 : ℝ)|=(2170081757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259643723/5000000000 : ℝ)|^4251 ≤ (17562481399933/50000000000000 : ℝ)^3227
        have hw : |(2259643723/5000000000 : ℝ)|=(2259643723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4070209/9765625 : ℝ)|^4251 ≤ (493318798401/1562500000000 : ℝ)^3227
        have hw : |(4070209/9765625 : ℝ)|=(4070209/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (917/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (441/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14671/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (917/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (917/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (917/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (917/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (917/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (917/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (441/4000 : ℝ) ^ (2125/512 : ℝ) ≤ (10604668849711461/100000000000000000000 : ℝ) := by
    have hpowers : (441/4000 : ℝ)^2125 ≤ (10604668849711461/100000000000000000000 : ℝ)^512 := by
      have hnat : (441 : ℕ)^2125*100000000000000000000^512 ≤ 10604668849711461^512*4000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 4000 10604668849711461 100000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/4000 : ℝ)) (X := (10604668849711461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (917/6250 : ℝ) ^ (2125/512 : ℝ) ≤ (34722027838363067/100000000000000000000 : ℝ) := by
    have hpowers : (917/6250 : ℝ)^2125 ≤ (34722027838363067/100000000000000000000 : ℝ)^512 := by
      have hnat : (917 : ℕ)^2125*100000000000000000000^512 ≤ 34722027838363067^512*6250^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        917 6250 34722027838363067 100000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (917/6250 : ℝ)) (X := (34722027838363067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010604668849711461/50000000000000000000 : ℝ) ≤ (10000510979147939/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50010604668849711461/50000000000000000000 : ℝ)^512 ≤ (10000510979147939/10000000000000000 : ℝ)^2125 := by
      have hnat : (50010604668849711461 : ℕ)^512*10000000000000000^2125 ≤ 10000510979147939^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010604668849711461 50000000000000000000 10000510979147939 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000510979147939/10000000000000000 : ℝ)) (X := (50010604668849711461/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126416459271502329/3125000000000000000 : ℝ) ≤ (10001091918939371/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (3126416459271502329/3125000000000000000 : ℝ)^512 ≤ (10001091918939371/10000000000000000 : ℝ)^2125 := by
      have hnat : (3126416459271502329 : ℕ)^512*10000000000000000^2125 ≤ 10001091918939371^2125*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126416459271502329 3125000000000000000 10001091918939371 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091918939371/10000000000000000 : ℝ)) (X := (3126416459271502329/3125000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034722027838363067/50000000000000000000 : ℝ) ≤ (10001672858730803/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50034722027838363067/50000000000000000000 : ℝ)^512 ≤ (10001672858730803/10000000000000000 : ℝ)^2125 := by
      have hnat : (50034722027838363067 : ℕ)^512*10000000000000000^2125 ≤ 10001672858730803^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034722027838363067 50000000000000000000 10001672858730803 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672858730803/10000000000000000 : ℝ)) (X := (50034722027838363067/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10604668849711461/100000000000000000000 : ℝ) ≤ ((5208436259793065419/5210000000000000000 : ℝ)+2*(10373924847/6512500000000 : ℝ)*(441/4000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (5208436259793065419/5210000000000000000 : ℝ)+2*(10373924847/6512500000000 : ℝ)*(441/4000 : ℝ)=(10000510979147939/10000000000000000 : ℝ) by norm_num, show 1+2*(10604668849711461/100000000000000000000 : ℝ)=(50010604668849711461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34722027838363067/100000000000000000000 : ℝ)+(10604668849711461/100000000000000000000 : ℝ) ≤ ((5208436259793065419/5210000000000000000 : ℝ)+(10373924847/6512500000000 : ℝ)*((917/6250 : ℝ)+(441/4000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (5208436259793065419/5210000000000000000 : ℝ)+(10373924847/6512500000000 : ℝ)*((917/6250 : ℝ)+(441/4000 : ℝ))=(10001091918939371/10000000000000000 : ℝ) by norm_num, show 1+(34722027838363067/100000000000000000000 : ℝ)+(10604668849711461/100000000000000000000 : ℝ)=(3126416459271502329/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34722027838363067/100000000000000000000 : ℝ) ≤ ((5208436259793065419/5210000000000000000 : ℝ)+2*(10373924847/6512500000000 : ℝ)*(917/6250 : ℝ))^(2125/512 : ℝ) := by
    rw [show (5208436259793065419/5210000000000000000 : ℝ)+2*(10373924847/6512500000000 : ℝ)*(917/6250 : ℝ)=(10001672858730803/10000000000000000 : ℝ) by norm_num, show 1+2*(34722027838363067/100000000000000000000 : ℝ)=(50034722027838363067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5208436259793065419/5210000000000000000 : ℝ)*(X 1 0+X 2 0)+(10373924847/6512500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (5208436259793065419/5210000000000000000 : ℝ)) (alpha := (10373924847/6512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5208436259793065419/5210000000000000000 : ℝ)*(X 0 1+X 2 1)+(10373924847/6512500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (5208436259793065419/5210000000000000000 : ℝ)) (alpha := (10373924847/6512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5208436259793065419/5210000000000000000 : ℝ)*(X 0 2+X 1 2)+(10373924847/6512500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (5208436259793065419/5210000000000000000 : ℝ)) (alpha := (10373924847/6512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1069958327/2000000000 : ℝ)*X 2 0+(1048596451/2000000000 : ℝ)*X 2 1+(-1088342171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-522220601/2500000000 : ℝ)*X 0 0+(2621798003/5000000000 : ℝ)*X 0 1+(1353658999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2652845743/5000000000 : ℝ)*X 1 0+(-10025153/50000000 : ℝ)*X 1 1+(1082927199/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652845743/5000000000 : ℝ)*X 2 0+(1082927199/2000000000 : ℝ)*X 2 1+(-10025153/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2170081757/5000000000 : ℝ)*X 0 0+(2259643723/5000000000 : ℝ)*X 0 1+(4070209/9765625 : ℝ)*X 0 2+(2170081757/5000000000 : ℝ)*X 1 0+(2259643723/5000000000 : ℝ)*X 1 1+(4070209/9765625 : ℝ)*X 1 2+(2170081757/5000000000 : ℝ)*X 2 0+(2259643723/5000000000 : ℝ)*X 2 1+(4070209/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (422276291226864679184300013/130250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115209001/20000000000000 : ℝ)*(base19) + (156580147/25000000000000 : ℝ)*(base23) + (197685003/100000000000000 : ℝ)*(lower1) + (8233493/12500000000000 : ℝ)*(upper3) + (11388733/50000000000000 : ℝ)*(lower4) + (33100219/50000000000000 : ℝ)*(upper5) + (2173095322394109/50000000000000 : ℝ)*(major0) + (2173095322394109/50000000000000 : ℝ)*(major1) + (2173095322394109/50000000000000 : ℝ)*(major2) + (883717017/100000000000000 : ℝ)*(sp0) + (584657393651857/10000000000000 : ℝ)*(sp1) + (1169314672094713/20000000000000 : ℝ)*(sp2) + (1461643106620241/25000000000000 : ℝ)*(sp3) + (2845807244989709/100000000000000 : ℝ)*(sp4) + (2845807244989709/100000000000000 : ℝ)*(f.failure) + (584657393651857/10000000000000 : ℝ)*(f.sum) + (5542468932919/1302500000000000000000000000 : ℝ)*base65 + (3817896990961383329/260500000000000000000000000000000 : ℝ)*base68 + (2191231423976383329/260500000000000000000000000000000 : ℝ)*base70 + (6636616500472383329/260500000000000000000000000000000 : ℝ)*base72 + (6898710278151/1302500000000000000000000000 : ℝ)*base74 + (1130006434496116671/260500000000000000000000000000000 : ℝ)*base75 + (99637966333116671/260500000000000000000000000000000 : ℝ)*base77 + (231437476208883329/260500000000000000000000000000000 : ℝ)*base80 + (3454289296241/1302500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (30892573/5000000000000000000000 : ℝ)*base89 + (30892573/5000000000000000000000 : ℝ)*base91 + (30892573/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1291_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (917/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1291_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1291_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1291_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1291_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1291_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
