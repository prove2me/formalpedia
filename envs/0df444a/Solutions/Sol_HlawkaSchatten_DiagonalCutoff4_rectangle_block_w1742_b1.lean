-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:41.869426+00:00
-- url     : https://prove2.me/submissions/1305b61c-30bd-46c9-9677-c2e1468e6930

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
theorem support_rectangle_w1742_s3_0 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19816731/156250000 : ℝ)*x 0 + (5508050249/10000000000 : ℝ)*x 1 + (158704917/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19816731/156250000 : ℝ)^5647 ≤ (4013676640807/50000000000000 : ℝ)^4623 := by
    have hnat : (19816731 : ℕ)^5647*50000000000000^4623 ≤ 4013676640807^4623*156250000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19816731 156250000 4013676640807 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508050249/10000000000 : ℝ)^5647 ≤ (2413229486741/5000000000000 : ℝ)^4623 := by
    have hnat : (5508050249 : ℕ)^5647*5000000000000^4623 ≤ 2413229486741^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508050249 10000000000 2413229486741 5000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158704917/312500000 : ℝ)^5647 ≤ (43708056962503/100000000000000 : ℝ)^4623 := by
    have hnat : (158704917 : ℕ)^5647*100000000000000^4623 ≤ 43708056962503^4623*312500000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158704917 312500000 43708056962503 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19816731/156250000 : ℝ), (5508050249/10000000000 : ℝ), (158704917/312500000 : ℝ)] ![(4013676640807/50000000000000 : ℝ), (2413229486741/5000000000000 : ℝ), (43708056962503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19816731/156250000 : ℝ)|^5647 ≤ (4013676640807/50000000000000 : ℝ)^4623
        have hw : |(-19816731/156250000 : ℝ)|=(19816731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508050249/10000000000 : ℝ)|^5647 ≤ (2413229486741/5000000000000 : ℝ)^4623
        have hw : |(5508050249/10000000000 : ℝ)|=(5508050249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158704917/312500000 : ℝ)|^5647 ≤ (43708056962503/100000000000000 : ℝ)^4623
        have hw : |(158704917/312500000 : ℝ)|=(158704917/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_1 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670956829/5000000000 : ℝ)*x 0 + (-1493269837/10000000000 : ℝ)*x 1 + (1015711291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670956829/5000000000 : ℝ)^5647 ≤ (46492338982149/100000000000000 : ℝ)^4623 := by
    have hnat : (2670956829 : ℕ)^5647*100000000000000^4623 ≤ 46492338982149^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670956829 5000000000 46492338982149 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493269837/10000000000 : ℝ)^5647 ≤ (2449903345341/25000000000000 : ℝ)^4623 := by
    have hnat : (1493269837 : ℕ)^5647*25000000000000^4623 ≤ 2449903345341^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493269837 10000000000 2449903345341 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015711291/2000000000 : ℝ)^5647 ≤ (43708047616697/100000000000000 : ℝ)^4623 := by
    have hnat : (1015711291 : ℕ)^5647*100000000000000^4623 ≤ 43708047616697^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015711291 2000000000 43708047616697 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670956829/5000000000 : ℝ), (-1493269837/10000000000 : ℝ), (1015711291/2000000000 : ℝ)] ![(46492338982149/100000000000000 : ℝ), (2449903345341/25000000000000 : ℝ), (43708047616697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670956829/5000000000 : ℝ)|^5647 ≤ (46492338982149/100000000000000 : ℝ)^4623
        have hw : |(2670956829/5000000000 : ℝ)|=(2670956829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1493269837/10000000000 : ℝ)|^5647 ≤ (2449903345341/25000000000000 : ℝ)^4623
        have hw : |(-1493269837/10000000000 : ℝ)|=(1493269837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015711291/2000000000 : ℝ)|^5647 ≤ (43708047616697/100000000000000 : ℝ)^4623
        have hw : |(1015711291/2000000000 : ℝ)|=(1015711291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_2 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670956071/5000000000 : ℝ)*x 0 + (5078558001/10000000000 : ℝ)*x 1 + (-746634911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670956071/5000000000 : ℝ)^5647 ≤ (46492322865393/100000000000000 : ℝ)^4623 := by
    have hnat : (2670956071 : ℕ)^5647*100000000000000^4623 ≤ 46492322865393^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670956071 5000000000 46492322865393 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078558001/10000000000 : ℝ)^5647 ≤ (43708063869359/100000000000000 : ℝ)^4623 := by
    have hnat : (5078558001 : ℕ)^5647*100000000000000^4623 ≤ 43708063869359^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078558001 10000000000 43708063869359 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746634911/5000000000 : ℝ)^5647 ≤ (4899806630561/50000000000000 : ℝ)^4623 := by
    have hnat : (746634911 : ℕ)^5647*50000000000000^4623 ≤ 4899806630561^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746634911 5000000000 4899806630561 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670956071/5000000000 : ℝ), (5078558001/10000000000 : ℝ), (-746634911/5000000000 : ℝ)] ![(46492322865393/100000000000000 : ℝ), (43708063869359/100000000000000 : ℝ), (4899806630561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670956071/5000000000 : ℝ)|^5647 ≤ (46492322865393/100000000000000 : ℝ)^4623
        have hw : |(2670956071/5000000000 : ℝ)|=(2670956071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078558001/10000000000 : ℝ)|^5647 ≤ (43708063869359/100000000000000 : ℝ)^4623
        have hw : |(5078558001/10000000000 : ℝ)|=(5078558001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-746634911/5000000000 : ℝ)|^5647 ≤ (4899806630561/50000000000000 : ℝ)^4623
        have hw : |(-746634911/5000000000 : ℝ)|=(746634911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_3 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4037941909/10000000000 : ℝ)*x 0 + (3387965207/10000000000 : ℝ)*x 1 + (594137271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037941909/10000000000 : ℝ)^5647 ≤ (33031177290479/100000000000000 : ℝ)^4623 := by
    have hnat : (4037941909 : ℕ)^5647*100000000000000^4623 ≤ 33031177290479^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037941909 10000000000 33031177290479 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3387965207/10000000000 : ℝ)^5647 ≤ (13328763507591/50000000000000 : ℝ)^4623 := by
    have hnat : (3387965207 : ℕ)^5647*50000000000000^4623 ≤ 13328763507591^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3387965207 10000000000 13328763507591 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594137271/1250000000 : ℝ)^5647 ≤ (4031129568371/10000000000000 : ℝ)^4623 := by
    have hnat : (594137271 : ℕ)^5647*10000000000000^4623 ≤ 4031129568371^4623*1250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594137271 1250000000 4031129568371 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037941909/10000000000 : ℝ), (3387965207/10000000000 : ℝ), (594137271/1250000000 : ℝ)] ![(33031177290479/100000000000000 : ℝ), (13328763507591/50000000000000 : ℝ), (4031129568371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037941909/10000000000 : ℝ)|^5647 ≤ (33031177290479/100000000000000 : ℝ)^4623
        have hw : |(4037941909/10000000000 : ℝ)|=(4037941909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3387965207/10000000000 : ℝ)|^5647 ≤ (13328763507591/50000000000000 : ℝ)^4623
        have hw : |(3387965207/10000000000 : ℝ)|=(3387965207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594137271/1250000000 : ℝ)|^5647 ≤ (4031129568371/10000000000000 : ℝ)^4623
        have hw : |(594137271/1250000000 : ℝ)|=(594137271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_4 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1268639961/10000000000 : ℝ)*x 0 + (5085451723/10000000000 : ℝ)*x 1 + (5501010051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1268639961/10000000000 : ℝ)^5647 ≤ (803020760331/10000000000000 : ℝ)^4623 := by
    have hnat : (1268639961 : ℕ)^5647*10000000000000^4623 ≤ 803020760331^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268639961 10000000000 803020760331 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085451723/10000000000 : ℝ)^5647 ≤ (21890273260603/50000000000000 : ℝ)^4623 := by
    have hnat : (5085451723 : ℕ)^5647*50000000000000^4623 ≤ 21890273260603^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085451723 10000000000 21890273260603 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501010051/10000000000 : ℝ)^5647 ≤ (48189245853211/100000000000000 : ℝ)^4623 := by
    have hnat : (5501010051 : ℕ)^5647*100000000000000^4623 ≤ 48189245853211^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501010051 10000000000 48189245853211 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1268639961/10000000000 : ℝ), (5085451723/10000000000 : ℝ), (5501010051/10000000000 : ℝ)] ![(803020760331/10000000000000 : ℝ), (21890273260603/50000000000000 : ℝ), (48189245853211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1268639961/10000000000 : ℝ)|^5647 ≤ (803020760331/10000000000000 : ℝ)^4623
        have hw : |(-1268639961/10000000000 : ℝ)|=(1268639961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085451723/10000000000 : ℝ)|^5647 ≤ (21890273260603/50000000000000 : ℝ)^4623
        have hw : |(5085451723/10000000000 : ℝ)|=(5085451723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501010051/10000000000 : ℝ)|^5647 ≤ (48189245853211/100000000000000 : ℝ)^4623
        have hw : |(5501010051/10000000000 : ℝ)|=(5501010051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_5 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227841553/10000000000 : ℝ)*x 0 + (-1070817643/10000000000 : ℝ)*x 1 + (1100202011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227841553/10000000000 : ℝ)^5647 ≤ (11320627625011/25000000000000 : ℝ)^4623 := by
    have hnat : (5227841553 : ℕ)^5647*25000000000000^4623 ≤ 11320627625011^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227841553 10000000000 11320627625011 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070817643/10000000000 : ℝ)^5647 ≤ (6528243590203/100000000000000 : ℝ)^4623 := by
    have hnat : (1070817643 : ℕ)^5647*100000000000000^4623 ≤ 6528243590203^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070817643 10000000000 6528243590203 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100202011/2000000000 : ℝ)^5647 ≤ (12047311474003/25000000000000 : ℝ)^4623 := by
    have hnat : (1100202011 : ℕ)^5647*25000000000000^4623 ≤ 12047311474003^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100202011 2000000000 12047311474003 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227841553/10000000000 : ℝ), (-1070817643/10000000000 : ℝ), (1100202011/2000000000 : ℝ)] ![(11320627625011/25000000000000 : ℝ), (6528243590203/100000000000000 : ℝ), (12047311474003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227841553/10000000000 : ℝ)|^5647 ≤ (11320627625011/25000000000000 : ℝ)^4623
        have hw : |(5227841553/10000000000 : ℝ)|=(5227841553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070817643/10000000000 : ℝ)|^5647 ≤ (6528243590203/100000000000000 : ℝ)^4623
        have hw : |(-1070817643/10000000000 : ℝ)|=(1070817643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100202011/2000000000 : ℝ)|^5647 ≤ (12047311474003/25000000000000 : ℝ)^4623
        have hw : |(1100202011/2000000000 : ℝ)|=(1100202011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_6 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209113661/400000000 : ℝ)*x 0 + (2750505017/5000000000 : ℝ)*x 1 + (-1070817713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209113661/400000000 : ℝ)^5647 ≤ (45282510203793/100000000000000 : ℝ)^4623 := by
    have hnat : (209113661 : ℕ)^5647*100000000000000^4623 ≤ 45282510203793^4623*400000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209113661 400000000 45282510203793 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750505017/5000000000 : ℝ)^5647 ≤ (48189245671303/100000000000000 : ℝ)^4623 := by
    have hnat : (2750505017 : ℕ)^5647*100000000000000^4623 ≤ 48189245671303^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750505017 5000000000 48189245671303 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070817713/10000000000 : ℝ)^5647 ≤ (1305648822297/20000000000000 : ℝ)^4623 := by
    have hnat : (1070817713 : ℕ)^5647*20000000000000^4623 ≤ 1305648822297^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070817713 10000000000 1305648822297 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209113661/400000000 : ℝ), (2750505017/5000000000 : ℝ), (-1070817713/10000000000 : ℝ)] ![(45282510203793/100000000000000 : ℝ), (48189245671303/100000000000000 : ℝ), (1305648822297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209113661/400000000 : ℝ)|^5647 ≤ (45282510203793/100000000000000 : ℝ)^4623
        have hw : |(209113661/400000000 : ℝ)|=(209113661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750505017/5000000000 : ℝ)|^5647 ≤ (48189245671303/100000000000000 : ℝ)^4623
        have hw : |(2750505017/5000000000 : ℝ)|=(2750505017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070817713/10000000000 : ℝ)|^5647 ≤ (1305648822297/20000000000000 : ℝ)^4623
        have hw : |(-1070817713/10000000000 : ℝ)|=(1070817713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s3_7 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039113877/10000000000 : ℝ)*x 0 + (295698997/625000000 : ℝ)*x 1 + (213146197/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039113877/10000000000 : ℝ)^5647 ≤ (33042888118223/100000000000000 : ℝ)^4623 := by
    have hnat : (4039113877 : ℕ)^5647*100000000000000^4623 ≤ 33042888118223^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039113877 10000000000 33042888118223 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295698997/625000000 : ℝ)^5647 ≤ (40084388772007/100000000000000 : ℝ)^4623 := by
    have hnat : (295698997 : ℕ)^5647*100000000000000^4623 ≤ 40084388772007^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295698997 625000000 40084388772007 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213146197/625000000 : ℝ)^5647 ≤ (26872723095921/100000000000000 : ℝ)^4623 := by
    have hnat : (213146197 : ℕ)^5647*100000000000000^4623 ≤ 26872723095921^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213146197 625000000 26872723095921 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039113877/10000000000 : ℝ), (295698997/625000000 : ℝ), (213146197/625000000 : ℝ)] ![(33042888118223/100000000000000 : ℝ), (40084388772007/100000000000000 : ℝ), (26872723095921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039113877/10000000000 : ℝ)|^5647 ≤ (33042888118223/100000000000000 : ℝ)^4623
        have hw : |(4039113877/10000000000 : ℝ)|=(4039113877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(295698997/625000000 : ℝ)|^5647 ≤ (40084388772007/100000000000000 : ℝ)^4623
        have hw : |(295698997/625000000 : ℝ)|=(295698997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(213146197/625000000 : ℝ)|^5647 ≤ (26872723095921/100000000000000 : ℝ)^4623
        have hw : |(213146197/625000000 : ℝ)|=(213146197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1742_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (893/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4533/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/3125 : ℝ) ^ (5631/1024 : ℝ) ≤ (169891891997217/100000000000000000000 : ℝ) := by
    have hpowers : (279/3125 : ℝ)^5631 ≤ (169891891997217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (279 : ℕ)^5631*100000000000000000000^1024 ≤ 169891891997217^1024*3125^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 3125 169891891997217 100000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/3125 : ℝ)) (X := (169891891997217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9067/50000 : ℝ) ^ (5631/1024 : ℝ) ≤ (4182240413371003/50000000000000000000 : ℝ) := by
    have hpowers : (9067/50000 : ℝ)^5631 ≤ (4182240413371003/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9067 : ℕ)^5631*50000000000000000000^1024 ≤ 4182240413371003^1024*50000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9067 50000 4182240413371003 50000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9067/50000 : ℝ)) (X := (4182240413371003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000169891891997217/50000000000000000000 : ℝ) ≤ (5000003089487757/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (50000169891891997217/50000000000000000000 : ℝ)^1024 ≤ (5000003089487757/5000000000000000 : ℝ)^5631 := by
      have hnat : (50000169891891997217 : ℕ)^1024*5000000000000000^5631 ≤ 5000003089487757^5631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000169891891997217 50000000000000000000 5000003089487757 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000003089487757/5000000000000000 : ℝ)) (X := (50000169891891997217/50000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008534372718739223/100000000000000000000 : ℝ) ≤ (500007759627577/500000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (100008534372718739223/100000000000000000000 : ℝ)^1024 ≤ (500007759627577/500000000000000 : ℝ)^5631 := by
      have hnat : (100008534372718739223 : ℕ)^1024*500000000000000^5631 ≤ 500007759627577^5631*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008534372718739223 100000000000000000000 500007759627577 500000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500007759627577/500000000000000 : ℝ)) (X := (100008534372718739223/100000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004182240413371003/25000000000000000000 : ℝ) ≤ (5000152103063783/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (25004182240413371003/25000000000000000000 : ℝ)^1024 ≤ (5000152103063783/5000000000000000 : ℝ)^5631 := by
      have hnat : (25004182240413371003 : ℕ)^1024*5000000000000000^5631 ≤ 5000152103063783^5631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004182240413371003 25000000000000000000 5000152103063783 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000152103063783/5000000000000000 : ℝ)) (X := (25004182240413371003/25000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(169891891997217/100000000000000000000 : ℝ) ≤ ((23014349024308765407/23015000000000000000 : ℝ)+2*(74506788013/460300000000000 : ℝ)*(279/3125 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (23014349024308765407/23015000000000000000 : ℝ)+2*(74506788013/460300000000000 : ℝ)*(279/3125 : ℝ)=(5000003089487757/5000000000000000 : ℝ) by norm_num, show 1+2*(169891891997217/100000000000000000000 : ℝ)=(50000169891891997217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4182240413371003/50000000000000000000 : ℝ)+(169891891997217/100000000000000000000 : ℝ) ≤ ((23014349024308765407/23015000000000000000 : ℝ)+(74506788013/460300000000000 : ℝ)*((9067/50000 : ℝ)+(279/3125 : ℝ)))^(5631/1024 : ℝ) := by
    rw [show (23014349024308765407/23015000000000000000 : ℝ)+(74506788013/460300000000000 : ℝ)*((9067/50000 : ℝ)+(279/3125 : ℝ))=(500007759627577/500000000000000 : ℝ) by norm_num, show 1+(4182240413371003/50000000000000000000 : ℝ)+(169891891997217/100000000000000000000 : ℝ)=(100008534372718739223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4182240413371003/50000000000000000000 : ℝ) ≤ ((23014349024308765407/23015000000000000000 : ℝ)+2*(74506788013/460300000000000 : ℝ)*(9067/50000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (23014349024308765407/23015000000000000000 : ℝ)+2*(74506788013/460300000000000 : ℝ)*(9067/50000 : ℝ)=(5000152103063783/5000000000000000 : ℝ) by norm_num, show 1+2*(4182240413371003/50000000000000000000 : ℝ)=(25004182240413371003/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23014349024308765407/23015000000000000000 : ℝ)*(X 1 0+X 2 0)+(74506788013/460300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (9067/50000 : ℝ)) (c := (23014349024308765407/23015000000000000000 : ℝ)) (alpha := (74506788013/460300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23014349024308765407/23015000000000000000 : ℝ)*(X 0 1+X 2 1)+(74506788013/460300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (9067/50000 : ℝ)) (c := (23014349024308765407/23015000000000000000 : ℝ)) (alpha := (74506788013/460300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23014349024308765407/23015000000000000000 : ℝ)*(X 0 2+X 1 2)+(74506788013/460300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (9067/50000 : ℝ)) (c := (23014349024308765407/23015000000000000000 : ℝ)) (alpha := (74506788013/460300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-19816731/156250000 : ℝ)*X 0 0+(5508050249/10000000000 : ℝ)*X 0 1+(158704917/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670956829/5000000000 : ℝ)*X 1 0+(-1493269837/10000000000 : ℝ)*X 1 1+(1015711291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2670956071/5000000000 : ℝ)*X 2 0+(5078558001/10000000000 : ℝ)*X 2 1+(-746634911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4037941909/10000000000 : ℝ)*X 0 0+(3387965207/10000000000 : ℝ)*X 0 1+(594137271/1250000000 : ℝ)*X 0 2+(4037941909/10000000000 : ℝ)*X 1 0+(3387965207/10000000000 : ℝ)*X 1 1+(594137271/1250000000 : ℝ)*X 1 2+(4037941909/10000000000 : ℝ)*X 2 0+(3387965207/10000000000 : ℝ)*X 2 1+(594137271/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1268639961/10000000000 : ℝ)*X 0 0+(5085451723/10000000000 : ℝ)*X 0 1+(5501010051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227841553/10000000000 : ℝ)*X 1 0+(-1070817643/10000000000 : ℝ)*X 1 1+(1100202011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((209113661/400000000 : ℝ)*X 2 0+(2750505017/5000000000 : ℝ)*X 2 1+(-1070817713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4039113877/10000000000 : ℝ)*X 0 0+(295698997/625000000 : ℝ)*X 0 1+(213146197/625000000 : ℝ)*X 0 2+(4039113877/10000000000 : ℝ)*X 1 0+(295698997/625000000 : ℝ)*X 1 1+(213146197/625000000 : ℝ)*X 1 2+(4039113877/10000000000 : ℝ)*X 2 0+(295698997/625000000 : ℝ)*X 2 1+(213146197/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2338937306921155273883787231/287687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1219691123/100000000000000 : ℝ)*(base19) + (647538733/100000000000000 : ℝ)*(base23) + (1009421/2000000000000 : ℝ)*(lower2) + (97809567/100000000000000 : ℝ)*(lower4) + (8554547/100000000000000 : ℝ)*(lower5) + (765220531262189/50000000000000 : ℝ)*(major0) + (765220531262189/50000000000000 : ℝ)*(major1) + (765220531262189/50000000000000 : ℝ)*(major2) + (291042275166409/12500000000000 : ℝ)*(sp0) + (2328346290942717/100000000000000 : ℝ)*(sp1) + (582086715773777/25000000000000 : ℝ)*(sp2) + (22891627920277/3125000000000 : ℝ)*(sp3) + (1163662821/12500000000000 : ℝ)*(sp4) + (44999233/2000000000000 : ℝ)*(sp7) + (146506868682103/20000000000000 : ℝ)*(f.failure) + (29104343882923/1250000000000 : ℝ)*(f.sum) + (14666408842741/5753750000000000000000000000 : ℝ)*base65 + (3454517537753145923/1150750000000000000000000000000000 : ℝ)*base67 + (8659075036967145923/1150750000000000000000000000000000 : ℝ)*base69 + (3996911844824145923/1150750000000000000000000000000000 : ℝ)*base71 + (6494598083871/23015000000000000000000000000 : ℝ)*base74 + (12001985721342895923/1150750000000000000000000000000000 : ℝ)*base75 + (6887512357911645923/1150750000000000000000000000000000 : ℝ)*base77 + (138524096433854077/1150750000000000000000000000000000 : ℝ)*base80 + (41503266532637/11507500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2651107/1000000000000000000000 : ℝ)*base89 + (2651107/1000000000000000000000 : ℝ)*base91 + (2651107/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49552425607096585445007/5753750000000000000000000000 : ℝ) := by norm_num
    linear_combination (27994259/2500000000000 : ℝ)*(base19) + (298560067/25000000000000 : ℝ)*(base23) + (164027197/50000000000000 : ℝ)*(lower1) + (176691719/100000000000000 : ℝ)*(upper3) + (22047061/50000000000000 : ℝ)*(lower4) + (90773133/50000000000000 : ℝ)*(upper5) + (790870402603809/50000000000000 : ℝ)*(major0) + (790870402603809/50000000000000 : ℝ)*(major1) + (790870402603809/50000000000000 : ℝ)*(major2) + (69056347/50000000000000 : ℝ)*(sp2) + (481278547180189/20000000000000 : ℝ)*(sp4) + (300798952016323/12500000000000 : ℝ)*(sp5) + (150399462721749/6250000000000 : ℝ)*(sp6) + (757088587441063/100000000000000 : ℝ)*(sp7) + (757088587441063/100000000000000 : ℝ)*(f.failure) + (481278547180189/20000000000000 : ℝ)*(f.sum) + (33472709555861/5753750000000000000000000000 : ℝ)*base65 + (3769923709963235263/1150750000000000000000000000000000 : ℝ)*base67 + (8948761817793235263/1150750000000000000000000000000000 : ℝ)*base69 + (11271631947580764737/1150750000000000000000000000000000 : ℝ)*base72 + (1570918950463/11507500000000000000000000000 : ℝ)*base74 + (20730949413900514737/1150750000000000000000000000000000 : ℝ)*base76 + (2515723370122235263/1150750000000000000000000000000000 : ℝ)*base77 + (2709095585723014737/1150750000000000000000000000000000 : ℝ)*base80 + (9118282126147/11507500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (43460653/5000000000000000000000 : ℝ)*base90 + (43460653/5000000000000000000000 : ℝ)*base92 + (43460653/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1742_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (893/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1742_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1742_box_0 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216965237/2500000000 : ℝ)*x 0 + (5434157709/10000000000 : ℝ)*x 1 + (5434157127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216965237/2500000000 : ℝ)^5647 ≤ (1262570388941/25000000000000 : ℝ)^4623 := by
    have hnat : (216965237 : ℕ)^5647*25000000000000^4623 ≤ 1262570388941^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216965237 2500000000 1262570388941 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434157709/10000000000 : ℝ)^5647 ≤ (296717889501/625000000000 : ℝ)^4623 := by
    have hnat : (5434157709 : ℕ)^5647*625000000000^4623 ≤ 296717889501^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434157709 10000000000 296717889501 625000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434157127/10000000000 : ℝ)^5647 ≤ (47474856109349/100000000000000 : ℝ)^4623 := by
    have hnat : (5434157127 : ℕ)^5647*100000000000000^4623 ≤ 47474856109349^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434157127 10000000000 47474856109349 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216965237/2500000000 : ℝ), (5434157709/10000000000 : ℝ), (5434157127/10000000000 : ℝ)] ![(1262570388941/25000000000000 : ℝ), (296717889501/625000000000 : ℝ), (47474856109349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216965237/2500000000 : ℝ)|^5647 ≤ (1262570388941/25000000000000 : ℝ)^4623
        have hw : |(-216965237/2500000000 : ℝ)|=(216965237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434157709/10000000000 : ℝ)|^5647 ≤ (296717889501/625000000000 : ℝ)^4623
        have hw : |(5434157709/10000000000 : ℝ)|=(5434157709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434157127/10000000000 : ℝ)|^5647 ≤ (47474856109349/100000000000000 : ℝ)^4623
        have hw : |(5434157127/10000000000 : ℝ)|=(5434157127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_1 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298763249/2500000000 : ℝ)*x 0 + (-605662637/5000000000 : ℝ)*x 1 + (5434157497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298763249/2500000000 : ℝ)^5647 ≤ (4493583590869/10000000000000 : ℝ)^4623 := by
    have hnat : (1298763249 : ℕ)^5647*10000000000000^4623 ≤ 4493583590869^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298763249 2500000000 4493583590869 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605662637/5000000000 : ℝ)^5647 ≤ (7589304020499/100000000000000 : ℝ)^4623 := by
    have hnat : (605662637 : ℕ)^5647*100000000000000^4623 ≤ 7589304020499^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605662637 5000000000 7589304020499 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434157497/10000000000 : ℝ)^5647 ≤ (47474860057803/100000000000000 : ℝ)^4623 := by
    have hnat : (5434157497 : ℕ)^5647*100000000000000^4623 ≤ 47474860057803^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434157497 10000000000 47474860057803 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298763249/2500000000 : ℝ), (-605662637/5000000000 : ℝ), (5434157497/10000000000 : ℝ)] ![(4493583590869/10000000000000 : ℝ), (7589304020499/100000000000000 : ℝ), (47474860057803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298763249/2500000000 : ℝ)|^5647 ≤ (4493583590869/10000000000000 : ℝ)^4623
        have hw : |(1298763249/2500000000 : ℝ)|=(1298763249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605662637/5000000000 : ℝ)|^5647 ≤ (7589304020499/100000000000000 : ℝ)^4623
        have hw : |(-605662637/5000000000 : ℝ)|=(605662637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434157497/10000000000 : ℝ)|^5647 ≤ (47474860057803/100000000000000 : ℝ)^4623
        have hw : |(5434157497/10000000000 : ℝ)|=(5434157497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_2 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298763337/2500000000 : ℝ)*x 0 + (5434157227/10000000000 : ℝ)*x 1 + (-302831291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298763337/2500000000 : ℝ)^5647 ≤ (11233959906951/25000000000000 : ℝ)^4623 := by
    have hnat : (1298763337 : ℕ)^5647*25000000000000^4623 ≤ 11233959906951^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298763337 2500000000 11233959906951 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434157227/10000000000 : ℝ)^5647 ≤ (23737428588249/50000000000000 : ℝ)^4623 := by
    have hnat : (5434157227 : ℕ)^5647*50000000000000^4623 ≤ 23737428588249^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434157227 10000000000 23737428588249 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302831291/2500000000 : ℝ)^5647 ≤ (7589303178663/100000000000000 : ℝ)^4623 := by
    have hnat : (302831291 : ℕ)^5647*100000000000000^4623 ≤ 7589303178663^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302831291 2500000000 7589303178663 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298763337/2500000000 : ℝ), (5434157227/10000000000 : ℝ), (-302831291/2500000000 : ℝ)] ![(11233959906951/25000000000000 : ℝ), (23737428588249/50000000000000 : ℝ), (7589303178663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298763337/2500000000 : ℝ)|^5647 ≤ (11233959906951/25000000000000 : ℝ)^4623
        have hw : |(1298763337/2500000000 : ℝ)|=(1298763337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434157227/10000000000 : ℝ)|^5647 ≤ (23737428588249/50000000000000 : ℝ)^4623
        have hw : |(5434157227/10000000000 : ℝ)|=(5434157227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302831291/2500000000 : ℝ)|^5647 ≤ (7589303178663/100000000000000 : ℝ)^4623
        have hw : |(-302831291/2500000000 : ℝ)|=(302831291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_3 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (913166207/2000000000 : ℝ)*x 0 + (1907132529/5000000000 : ℝ)*x 1 + (3814265061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913166207/2000000000 : ℝ)^5647 ≤ (38379832438319/100000000000000 : ℝ)^4623 := by
    have hnat : (913166207 : ℕ)^5647*100000000000000^4623 ≤ 38379832438319^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913166207 2000000000 38379832438319 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907132529/5000000000 : ℝ)^5647 ≤ (30810083760839/100000000000000 : ℝ)^4623 := by
    have hnat : (1907132529 : ℕ)^5647*100000000000000^4623 ≤ 30810083760839^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907132529 5000000000 30810083760839 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3814265061/10000000000 : ℝ)^5647 ≤ (30810083790439/100000000000000 : ℝ)^4623 := by
    have hnat : (3814265061 : ℕ)^5647*100000000000000^4623 ≤ 30810083790439^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3814265061 10000000000 30810083790439 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(913166207/2000000000 : ℝ), (1907132529/5000000000 : ℝ), (3814265061/10000000000 : ℝ)] ![(38379832438319/100000000000000 : ℝ), (30810083760839/100000000000000 : ℝ), (30810083790439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(913166207/2000000000 : ℝ)|^5647 ≤ (38379832438319/100000000000000 : ℝ)^4623
        have hw : |(913166207/2000000000 : ℝ)|=(913166207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1907132529/5000000000 : ℝ)|^5647 ≤ (30810083760839/100000000000000 : ℝ)^4623
        have hw : |(1907132529/5000000000 : ℝ)|=(1907132529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3814265061/10000000000 : ℝ)|^5647 ≤ (30810083790439/100000000000000 : ℝ)^4623
        have hw : |(3814265061/10000000000 : ℝ)|=(3814265061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_4 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1708988249/10000000000 : ℝ)*x 0 + (5127415473/10000000000 : ℝ)*x 1 + (1025483109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1708988249/10000000000 : ℝ)^5647 ≤ (11555529993621/100000000000000 : ℝ)^4623 := by
    have hnat : (1708988249 : ℕ)^5647*100000000000000^4623 ≤ 11555529993621^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708988249 10000000000 11555529993621 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127415473/10000000000 : ℝ)^5647 ≤ (11055558654497/25000000000000 : ℝ)^4623 := by
    have hnat : (5127415473 : ℕ)^5647*25000000000000^4623 ≤ 11055558654497^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127415473 10000000000 11055558654497 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025483109/2000000000 : ℝ)^5647 ≤ (44222235376511/100000000000000 : ℝ)^4623 := by
    have hnat : (1025483109 : ℕ)^5647*100000000000000^4623 ≤ 44222235376511^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025483109 2000000000 44222235376511 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1708988249/10000000000 : ℝ), (5127415473/10000000000 : ℝ), (1025483109/2000000000 : ℝ)] ![(11555529993621/100000000000000 : ℝ), (11055558654497/25000000000000 : ℝ), (44222235376511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1708988249/10000000000 : ℝ)|^5647 ≤ (11555529993621/100000000000000 : ℝ)^4623
        have hw : |(-1708988249/10000000000 : ℝ)|=(1708988249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127415473/10000000000 : ℝ)|^5647 ≤ (11055558654497/25000000000000 : ℝ)^4623
        have hw : |(5127415473/10000000000 : ℝ)|=(5127415473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025483109/2000000000 : ℝ)|^5647 ≤ (44222235376511/100000000000000 : ℝ)^4623
        have hw : |(1025483109/2000000000 : ℝ)|=(1025483109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_5 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401099417/10000000000 : ℝ)*x 0 + (-26979031/200000000 : ℝ)*x 1 + (512741541/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401099417/10000000000 : ℝ)^5647 ≤ (47122318897579/100000000000000 : ℝ)^4623 := by
    have hnat : (5401099417 : ℕ)^5647*100000000000000^4623 ≤ 47122318897579^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401099417 10000000000 47122318897579 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26979031/200000000 : ℝ)^5647 ≤ (33810340381/390625000000 : ℝ)^4623 := by
    have hnat : (26979031 : ℕ)^5647*390625000000^4623 ≤ 33810340381^4623*200000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26979031 200000000 33810340381 390625000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512741541/1000000000 : ℝ)^5647 ≤ (44222233954281/100000000000000 : ℝ)^4623 := by
    have hnat : (512741541 : ℕ)^5647*100000000000000^4623 ≤ 44222233954281^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512741541 1000000000 44222233954281 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401099417/10000000000 : ℝ), (-26979031/200000000 : ℝ), (512741541/1000000000 : ℝ)] ![(47122318897579/100000000000000 : ℝ), (33810340381/390625000000 : ℝ), (44222233954281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401099417/10000000000 : ℝ)|^5647 ≤ (47122318897579/100000000000000 : ℝ)^4623
        have hw : |(5401099417/10000000000 : ℝ)|=(5401099417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26979031/200000000 : ℝ)|^5647 ≤ (33810340381/390625000000 : ℝ)^4623
        have hw : |(-26979031/200000000 : ℝ)|=(26979031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512741541/1000000000 : ℝ)|^5647 ≤ (44222233954281/100000000000000 : ℝ)^4623
        have hw : |(512741541/1000000000 : ℝ)|=(512741541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_6 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080219917/2000000000 : ℝ)*x 0 + (2563707679/5000000000 : ℝ)*x 1 + (-42154731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080219917/2000000000 : ℝ)^5647 ≤ (47122320687969/100000000000000 : ℝ)^4623 := by
    have hnat : (1080219917 : ℕ)^5647*100000000000000^4623 ≤ 47122320687969^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080219917 2000000000 47122320687969 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563707679/5000000000 : ℝ)^5647 ≤ (44222233406459/100000000000000 : ℝ)^4623 := by
    have hnat : (2563707679 : ℕ)^5647*100000000000000^4623 ≤ 44222233406459^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563707679 5000000000 44222233406459 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42154731/312500000 : ℝ)^5647 ≤ (540965368699/6250000000000 : ℝ)^4623 := by
    have hnat : (42154731 : ℕ)^5647*6250000000000^4623 ≤ 540965368699^4623*312500000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42154731 312500000 540965368699 6250000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080219917/2000000000 : ℝ), (2563707679/5000000000 : ℝ), (-42154731/312500000 : ℝ)] ![(47122320687969/100000000000000 : ℝ), (44222233406459/100000000000000 : ℝ), (540965368699/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080219917/2000000000 : ℝ)|^5647 ≤ (47122320687969/100000000000000 : ℝ)^4623
        have hw : |(1080219917/2000000000 : ℝ)|=(1080219917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563707679/5000000000 : ℝ)|^5647 ≤ (44222233406459/100000000000000 : ℝ)^4623
        have hw : |(2563707679/5000000000 : ℝ)|=(2563707679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42154731/312500000 : ℝ)|^5647 ≤ (540965368699/6250000000000 : ℝ)^4623
        have hw : |(-42154731/312500000 : ℝ)|=(42154731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_7 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (694971751/2000000000 : ℝ)*x 0 + (4357579813/10000000000 : ℝ)*x 1 + (435758011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (694971751/2000000000 : ℝ)^5647 ≤ (27495029511783/100000000000000 : ℝ)^4623 := by
    have hnat : (694971751 : ℕ)^5647*100000000000000^4623 ≤ 27495029511783^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694971751 2000000000 27495029511783 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4357579813/10000000000 : ℝ)^5647 ≤ (9063120931519/25000000000000 : ℝ)^4623 := by
    have hnat : (4357579813 : ℕ)^5647*25000000000000^4623 ≤ 9063120931519^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357579813 10000000000 9063120931519 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435758011/1000000000 : ℝ)^5647 ≤ (36252486744239/100000000000000 : ℝ)^4623 := by
    have hnat : (435758011 : ℕ)^5647*100000000000000^4623 ≤ 36252486744239^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435758011 1000000000 36252486744239 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(694971751/2000000000 : ℝ), (4357579813/10000000000 : ℝ), (435758011/1000000000 : ℝ)] ![(27495029511783/100000000000000 : ℝ), (9063120931519/25000000000000 : ℝ), (36252486744239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(694971751/2000000000 : ℝ)|^5647 ≤ (27495029511783/100000000000000 : ℝ)^4623
        have hw : |(694971751/2000000000 : ℝ)|=(694971751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4357579813/10000000000 : ℝ)|^5647 ≤ (9063120931519/25000000000000 : ℝ)^4623
        have hw : |(4357579813/10000000000 : ℝ)|=(4357579813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(435758011/1000000000 : ℝ)|^5647 ≤ (36252486744239/100000000000000 : ℝ)^4623
        have hw : |(435758011/1000000000 : ℝ)|=(435758011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_8 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1526323183/10000000000 : ℝ)*x 0 + (2447363179/5000000000 : ℝ)*x 1 + (5497479117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526323183/10000000000 : ℝ)^5647 ≤ (5032609507087/50000000000000 : ℝ)^4623 := by
    have hnat : (1526323183 : ℕ)^5647*50000000000000^4623 ≤ 5032609507087^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526323183 10000000000 5032609507087 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2447363179/5000000000 : ℝ)^5647 ≤ (41783314969051/100000000000000 : ℝ)^4623 := by
    have hnat : (2447363179 : ℕ)^5647*100000000000000^4623 ≤ 41783314969051^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447363179 5000000000 41783314969051 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497479117/10000000000 : ℝ)^5647 ≤ (4815146599651/10000000000000 : ℝ)^4623 := by
    have hnat : (5497479117 : ℕ)^5647*10000000000000^4623 ≤ 4815146599651^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497479117 10000000000 4815146599651 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1526323183/10000000000 : ℝ), (2447363179/5000000000 : ℝ), (5497479117/10000000000 : ℝ)] ![(5032609507087/50000000000000 : ℝ), (41783314969051/100000000000000 : ℝ), (4815146599651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1526323183/10000000000 : ℝ)|^5647 ≤ (5032609507087/50000000000000 : ℝ)^4623
        have hw : |(-1526323183/10000000000 : ℝ)|=(1526323183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2447363179/5000000000 : ℝ)|^5647 ≤ (41783314969051/100000000000000 : ℝ)^4623
        have hw : |(2447363179/5000000000 : ℝ)|=(2447363179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497479117/10000000000 : ℝ)|^5647 ≤ (4815146599651/10000000000000 : ℝ)^4623
        have hw : |(5497479117/10000000000 : ℝ)|=(5497479117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_9 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152576723/10000000000 : ℝ)*x 0 + (-1181420239/10000000000 : ℝ)*x 1 + (2748740117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152576723/10000000000 : ℝ)^5647 ≤ (44487453198523/100000000000000 : ℝ)^4623 := by
    have hnat : (5152576723 : ℕ)^5647*100000000000000^4623 ≤ 44487453198523^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152576723 10000000000 44487453198523 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181420239/10000000000 : ℝ)^5647 ≤ (1472213767209/20000000000000 : ℝ)^4623 := by
    have hnat : (1181420239 : ℕ)^5647*20000000000000^4623 ≤ 1472213767209^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181420239 10000000000 1472213767209 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748740117/5000000000 : ℝ)^5647 ≤ (48151477947201/100000000000000 : ℝ)^4623 := by
    have hnat : (2748740117 : ℕ)^5647*100000000000000^4623 ≤ 48151477947201^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748740117 5000000000 48151477947201 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152576723/10000000000 : ℝ), (-1181420239/10000000000 : ℝ), (2748740117/5000000000 : ℝ)] ![(44487453198523/100000000000000 : ℝ), (1472213767209/20000000000000 : ℝ), (48151477947201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152576723/10000000000 : ℝ)|^5647 ≤ (44487453198523/100000000000000 : ℝ)^4623
        have hw : |(5152576723/10000000000 : ℝ)|=(5152576723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1181420239/10000000000 : ℝ)|^5647 ≤ (1472213767209/20000000000000 : ℝ)^4623
        have hw : |(-1181420239/10000000000 : ℝ)|=(1181420239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748740117/5000000000 : ℝ)|^5647 ≤ (48151477947201/100000000000000 : ℝ)^4623
        have hw : |(2748740117/5000000000 : ℝ)|=(2748740117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_10 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152576711/10000000000 : ℝ)*x 0 + (5497480077/10000000000 : ℝ)*x 1 + (-590710239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152576711/10000000000 : ℝ)^5647 ≤ (22243726535983/50000000000000 : ℝ)^4623 := by
    have hnat : (5152576711 : ℕ)^5647*50000000000000^4623 ≤ 22243726535983^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152576711 10000000000 22243726535983 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497480077/10000000000 : ℝ)^5647 ≤ (48151476267471/100000000000000 : ℝ)^4623 := by
    have hnat : (5497480077 : ℕ)^5647*100000000000000^4623 ≤ 48151476267471^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497480077 10000000000 48151476267471 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590710239/5000000000 : ℝ)^5647 ≤ (3680535327513/50000000000000 : ℝ)^4623 := by
    have hnat : (590710239 : ℕ)^5647*50000000000000^4623 ≤ 3680535327513^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590710239 5000000000 3680535327513 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152576711/10000000000 : ℝ), (5497480077/10000000000 : ℝ), (-590710239/5000000000 : ℝ)] ![(22243726535983/50000000000000 : ℝ), (48151476267471/100000000000000 : ℝ), (3680535327513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152576711/10000000000 : ℝ)|^5647 ≤ (22243726535983/50000000000000 : ℝ)^4623
        have hw : |(5152576711/10000000000 : ℝ)|=(5152576711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497480077/10000000000 : ℝ)|^5647 ≤ (48151476267471/100000000000000 : ℝ)^4623
        have hw : |(5497480077/10000000000 : ℝ)|=(5497480077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-590710239/5000000000 : ℝ)|^5647 ≤ (3680535327513/50000000000000 : ℝ)^4623
        have hw : |(-590710239/5000000000 : ℝ)|=(590710239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_11 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4780379207/10000000000 : ℝ)*x 0 + (3701686383/10000000000 : ℝ)*x 1 + (3701686203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4780379207/10000000000 : ℝ)^5647 ≤ (40594096294767/100000000000000 : ℝ)^4623 := by
    have hnat : (4780379207 : ℕ)^5647*100000000000000^4623 ≤ 40594096294767^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780379207 10000000000 40594096294767 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3701686383/10000000000 : ℝ)^5647 ≤ (3712869090633/12500000000000 : ℝ)^4623 := by
    have hnat : (3701686383 : ℕ)^5647*12500000000000^4623 ≤ 3712869090633^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701686383 10000000000 3712869090633 12500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3701686203/10000000000 : ℝ)^5647 ≤ (29702950960789/100000000000000 : ℝ)^4623 := by
    have hnat : (3701686203 : ℕ)^5647*100000000000000^4623 ≤ 29702950960789^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701686203 10000000000 29702950960789 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4780379207/10000000000 : ℝ), (3701686383/10000000000 : ℝ), (3701686203/10000000000 : ℝ)] ![(40594096294767/100000000000000 : ℝ), (3712869090633/12500000000000 : ℝ), (29702950960789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4780379207/10000000000 : ℝ)|^5647 ≤ (40594096294767/100000000000000 : ℝ)^4623
        have hw : |(4780379207/10000000000 : ℝ)|=(4780379207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3701686383/10000000000 : ℝ)|^5647 ≤ (3712869090633/12500000000000 : ℝ)^4623
        have hw : |(3701686383/10000000000 : ℝ)|=(3701686383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3701686203/10000000000 : ℝ)|^5647 ≤ (29702950960789/100000000000000 : ℝ)^4623
        have hw : |(3701686203/10000000000 : ℝ)|=(3701686203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_12 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259332953/2500000000 : ℝ)*x 0 + (565276421/1000000000 : ℝ)*x 1 + (5097021431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259332953/2500000000 : ℝ)^5647 ≤ (6279749148551/100000000000000 : ℝ)^4623 := by
    have hnat : (259332953 : ℕ)^5647*100000000000000^4623 ≤ 6279749148551^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259332953 2500000000 6279749148551 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565276421/1000000000 : ℝ)^5647 ≤ (24909004023533/50000000000000 : ℝ)^4623 := by
    have hnat : (565276421 : ℕ)^5647*50000000000000^4623 ≤ 24909004023533^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565276421 1000000000 24909004023533 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097021431/10000000000 : ℝ)^5647 ≤ (10975560698953/25000000000000 : ℝ)^4623 := by
    have hnat : (5097021431 : ℕ)^5647*25000000000000^4623 ≤ 10975560698953^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097021431 10000000000 10975560698953 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259332953/2500000000 : ℝ), (565276421/1000000000 : ℝ), (5097021431/10000000000 : ℝ)] ![(6279749148551/100000000000000 : ℝ), (24909004023533/50000000000000 : ℝ), (10975560698953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259332953/2500000000 : ℝ)|^5647 ≤ (6279749148551/100000000000000 : ℝ)^4623
        have hw : |(-259332953/2500000000 : ℝ)|=(259332953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565276421/1000000000 : ℝ)|^5647 ≤ (24909004023533/50000000000000 : ℝ)^4623
        have hw : |(565276421/1000000000 : ℝ)|=(565276421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097021431/10000000000 : ℝ)|^5647 ≤ (10975560698953/25000000000000 : ℝ)^4623
        have hw : |(5097021431/10000000000 : ℝ)|=(5097021431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_13 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421586289/10000000000 : ℝ)*x 0 + (-272379299/2000000000 : ℝ)*x 1 + (5097021757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421586289/10000000000 : ℝ)^5647 ≤ (9468148167007/20000000000000 : ℝ)^4623 := by
    have hnat : (5421586289 : ℕ)^5647*20000000000000^4623 ≤ 9468148167007^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421586289 10000000000 9468148167007 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272379299/2000000000 : ℝ)^5647 ≤ (2189253231171/25000000000000 : ℝ)^4623 := by
    have hnat : (272379299 : ℕ)^5647*25000000000000^4623 ≤ 2189253231171^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272379299 2000000000 2189253231171 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097021757/10000000000 : ℝ)^5647 ≤ (21951123112857/50000000000000 : ℝ)^4623 := by
    have hnat : (5097021757 : ℕ)^5647*50000000000000^4623 ≤ 21951123112857^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097021757 10000000000 21951123112857 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421586289/10000000000 : ℝ), (-272379299/2000000000 : ℝ), (5097021757/10000000000 : ℝ)] ![(9468148167007/20000000000000 : ℝ), (2189253231171/25000000000000 : ℝ), (21951123112857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421586289/10000000000 : ℝ)|^5647 ≤ (9468148167007/20000000000000 : ℝ)^4623
        have hw : |(5421586289/10000000000 : ℝ)|=(5421586289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272379299/2000000000 : ℝ)|^5647 ≤ (2189253231171/25000000000000 : ℝ)^4623
        have hw : |(-272379299/2000000000 : ℝ)|=(272379299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097021757/10000000000 : ℝ)|^5647 ≤ (21951123112857/50000000000000 : ℝ)^4623
        have hw : |(5097021757/10000000000 : ℝ)|=(5097021757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_14 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (677698301/1250000000 : ℝ)*x 0 + (5097021523/10000000000 : ℝ)*x 1 + (-1361896647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677698301/1250000000 : ℝ)^5647 ≤ (47340742104291/100000000000000 : ℝ)^4623 := by
    have hnat : (677698301 : ℕ)^5647*100000000000000^4623 ≤ 47340742104291^4623*1250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677698301 1250000000 47340742104291 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097021523/10000000000 : ℝ)^5647 ≤ (548778047047/1250000000000 : ℝ)^4623 := by
    have hnat : (5097021523 : ℕ)^5647*1250000000000^4623 ≤ 548778047047^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097021523 10000000000 548778047047 1250000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361896647/10000000000 : ℝ)^5647 ≤ (8757014118533/100000000000000 : ℝ)^4623 := by
    have hnat : (1361896647 : ℕ)^5647*100000000000000^4623 ≤ 8757014118533^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361896647 10000000000 8757014118533 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677698301/1250000000 : ℝ), (5097021523/10000000000 : ℝ), (-1361896647/10000000000 : ℝ)] ![(47340742104291/100000000000000 : ℝ), (548778047047/1250000000000 : ℝ), (8757014118533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677698301/1250000000 : ℝ)|^5647 ≤ (47340742104291/100000000000000 : ℝ)^4623
        have hw : |(677698301/1250000000 : ℝ)|=(677698301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5097021523/10000000000 : ℝ)|^5647 ≤ (548778047047/1250000000000 : ℝ)^4623
        have hw : |(5097021523/10000000000 : ℝ)|=(5097021523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361896647/10000000000 : ℝ)|^5647 ≤ (8757014118533/100000000000000 : ℝ)^4623
        have hw : |(-1361896647/10000000000 : ℝ)|=(1361896647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_box_15 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3361541483/10000000000 : ℝ)*x 0 + (2205599387/5000000000 : ℝ)*x 1 + (2205599277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3361541483/10000000000 : ℝ)^5647 ≤ (26403784770611/100000000000000 : ℝ)^4623 := by
    have hnat : (3361541483 : ℕ)^5647*100000000000000^4623 ≤ 26403784770611^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3361541483 10000000000 26403784770611 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205599387/5000000000 : ℝ)^5647 ≤ (18399054364469/50000000000000 : ℝ)^4623 := by
    have hnat : (2205599387 : ℕ)^5647*50000000000000^4623 ≤ 18399054364469^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205599387 5000000000 18399054364469 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205599277/5000000000 : ℝ)^5647 ≤ (36798106487197/100000000000000 : ℝ)^4623 := by
    have hnat : (2205599277 : ℕ)^5647*100000000000000^4623 ≤ 36798106487197^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205599277 5000000000 36798106487197 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3361541483/10000000000 : ℝ), (2205599387/5000000000 : ℝ), (2205599277/5000000000 : ℝ)] ![(26403784770611/100000000000000 : ℝ), (18399054364469/50000000000000 : ℝ), (36798106487197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3361541483/10000000000 : ℝ)|^5647 ≤ (26403784770611/100000000000000 : ℝ)^4623
        have hw : |(3361541483/10000000000 : ℝ)|=(3361541483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205599387/5000000000 : ℝ)|^5647 ≤ (18399054364469/50000000000000 : ℝ)^4623
        have hw : |(2205599387/5000000000 : ℝ)|=(2205599387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205599277/5000000000 : ℝ)|^5647 ≤ (36798106487197/100000000000000 : ℝ)^4623
        have hw : |(2205599277/5000000000 : ℝ)|=(2205599277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1742_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (893/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68767/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3607/6250 : ℝ) ∧ (2534/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (23187/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (893/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4533/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (893/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (893/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4533/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (893/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (893/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4533/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (893/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (893/10000 : ℝ) ^ (5631/1024 : ℝ) ≤ (42525320132123/25000000000000000000 : ℝ) := by
    have hpowers : (893/10000 : ℝ)^5631 ≤ (42525320132123/25000000000000000000 : ℝ)^1024 := by
      have hnat : (893 : ℕ)^5631*25000000000000000000^1024 ≤ 42525320132123^1024*10000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        893 10000 42525320132123 25000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (893/10000 : ℝ)) (X := (42525320132123/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4533/25000 : ℝ) ^ (5631/1024 : ℝ) ≤ (83594091309323/1000000000000000000 : ℝ) := by
    have hpowers : (4533/25000 : ℝ)^5631 ≤ (83594091309323/1000000000000000000 : ℝ)^1024 := by
      have hnat : (4533 : ℕ)^5631*1000000000000000000^1024 ≤ 83594091309323^1024*25000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4533 25000 83594091309323 1000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4533/25000 : ℝ)) (X := (83594091309323/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500042525320132123/12500000000000000000 : ℝ) ≤ (5000003093295487/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (12500042525320132123/12500000000000000000 : ℝ)^1024 ≤ (5000003093295487/5000000000000000 : ℝ)^5631 := by
      have hnat : (12500042525320132123 : ℕ)^1024*5000000000000000^5631 ≤ 5000003093295487^5631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500042525320132123 12500000000000000000 5000003093295487 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000003093295487/5000000000000000 : ℝ)) (X := (12500042525320132123/12500000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501066188801432599/12500000000000000000 : ℝ) ≤ (400006204165457/400000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (12501066188801432599/12500000000000000000 : ℝ)^1024 ≤ (400006204165457/400000000000000 : ℝ)^5631 := by
      have hnat : (12501066188801432599 : ℕ)^1024*400000000000000^5631 ≤ 400006204165457^5631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501066188801432599 12500000000000000000 400006204165457 400000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400006204165457/400000000000000 : ℝ)) (X := (12501066188801432599/12500000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500083594091309323/500000000000000000 : ℝ) ≤ (2500076005420469/2500000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (500083594091309323/500000000000000000 : ℝ)^1024 ≤ (2500076005420469/2500000000000000 : ℝ)^5631 := by
      have hnat : (500083594091309323 : ℕ)^1024*2500000000000000^5631 ≤ 2500076005420469^5631*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500083594091309323 500000000000000000 2500076005420469 2500000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500076005420469/2500000000000000 : ℝ)) (X := (500083594091309323/500000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(42525320132123/25000000000000000000 : ℝ) ≤ ((5751087328853024243/5751250000000000000 : ℝ)+2*(148917545451/920200000000000 : ℝ)*(893/10000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (5751087328853024243/5751250000000000000 : ℝ)+2*(148917545451/920200000000000 : ℝ)*(893/10000 : ℝ)=(5000003093295487/5000000000000000 : ℝ) by norm_num, show 1+2*(42525320132123/25000000000000000000 : ℝ)=(12500042525320132123/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83594091309323/1000000000000000000 : ℝ)+(42525320132123/25000000000000000000 : ℝ) ≤ ((5751087328853024243/5751250000000000000 : ℝ)+(148917545451/920200000000000 : ℝ)*((4533/25000 : ℝ)+(893/10000 : ℝ)))^(5631/1024 : ℝ) := by
    rw [show (5751087328853024243/5751250000000000000 : ℝ)+(148917545451/920200000000000 : ℝ)*((4533/25000 : ℝ)+(893/10000 : ℝ))=(400006204165457/400000000000000 : ℝ) by norm_num, show 1+(83594091309323/1000000000000000000 : ℝ)+(42525320132123/25000000000000000000 : ℝ)=(12501066188801432599/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83594091309323/1000000000000000000 : ℝ) ≤ ((5751087328853024243/5751250000000000000 : ℝ)+2*(148917545451/920200000000000 : ℝ)*(4533/25000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (5751087328853024243/5751250000000000000 : ℝ)+2*(148917545451/920200000000000 : ℝ)*(4533/25000 : ℝ)=(2500076005420469/2500000000000000 : ℝ) by norm_num, show 1+2*(83594091309323/1000000000000000000 : ℝ)=(500083594091309323/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5751087328853024243/5751250000000000000 : ℝ)*(X 1 0+X 2 0)+(148917545451/920200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (893/10000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (5751087328853024243/5751250000000000000 : ℝ)) (alpha := (148917545451/920200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5751087328853024243/5751250000000000000 : ℝ)*(X 0 1+X 2 1)+(148917545451/920200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (893/10000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (5751087328853024243/5751250000000000000 : ℝ)) (alpha := (148917545451/920200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5751087328853024243/5751250000000000000 : ℝ)*(X 0 2+X 1 2)+(148917545451/920200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (893/10000 : ℝ)) (hi := (4533/25000 : ℝ)) (c := (5751087328853024243/5751250000000000000 : ℝ)) (alpha := (148917545451/920200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216965237/2500000000 : ℝ)*X 0 0+(5434157709/10000000000 : ℝ)*X 0 1+(5434157127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1298763249/2500000000 : ℝ)*X 1 0+(-605662637/5000000000 : ℝ)*X 1 1+(5434157497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1298763337/2500000000 : ℝ)*X 2 0+(5434157227/10000000000 : ℝ)*X 2 1+(-302831291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((913166207/2000000000 : ℝ)*X 0 0+(1907132529/5000000000 : ℝ)*X 0 1+(3814265061/10000000000 : ℝ)*X 0 2+(913166207/2000000000 : ℝ)*X 1 0+(1907132529/5000000000 : ℝ)*X 1 1+(3814265061/10000000000 : ℝ)*X 1 2+(913166207/2000000000 : ℝ)*X 2 0+(1907132529/5000000000 : ℝ)*X 2 1+(3814265061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1708988249/10000000000 : ℝ)*X 0 0+(5127415473/10000000000 : ℝ)*X 0 1+(1025483109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5401099417/10000000000 : ℝ)*X 1 0+(-26979031/200000000 : ℝ)*X 1 1+(512741541/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1080219917/2000000000 : ℝ)*X 2 0+(2563707679/5000000000 : ℝ)*X 2 1+(-42154731/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((694971751/2000000000 : ℝ)*X 0 0+(4357579813/10000000000 : ℝ)*X 0 1+(435758011/1000000000 : ℝ)*X 0 2+(694971751/2000000000 : ℝ)*X 1 0+(4357579813/10000000000 : ℝ)*X 1 1+(435758011/1000000000 : ℝ)*X 1 2+(694971751/2000000000 : ℝ)*X 2 0+(4357579813/10000000000 : ℝ)*X 2 1+(435758011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1526323183/10000000000 : ℝ)*X 0 0+(2447363179/5000000000 : ℝ)*X 0 1+(5497479117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152576723/10000000000 : ℝ)*X 1 0+(-1181420239/10000000000 : ℝ)*X 1 1+(2748740117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152576711/10000000000 : ℝ)*X 2 0+(5497480077/10000000000 : ℝ)*X 2 1+(-590710239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4780379207/10000000000 : ℝ)*X 0 0+(3701686383/10000000000 : ℝ)*X 0 1+(3701686203/10000000000 : ℝ)*X 0 2+(4780379207/10000000000 : ℝ)*X 1 0+(3701686383/10000000000 : ℝ)*X 1 1+(3701686203/10000000000 : ℝ)*X 1 2+(4780379207/10000000000 : ℝ)*X 2 0+(3701686383/10000000000 : ℝ)*X 2 1+(3701686203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-259332953/2500000000 : ℝ)*X 0 0+(565276421/1000000000 : ℝ)*X 0 1+(5097021431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5421586289/10000000000 : ℝ)*X 1 0+(-272379299/2000000000 : ℝ)*X 1 1+(5097021757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((677698301/1250000000 : ℝ)*X 2 0+(5097021523/10000000000 : ℝ)*X 2 1+(-1361896647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3361541483/10000000000 : ℝ)*X 0 0+(2205599387/5000000000 : ℝ)*X 0 1+(2205599277/5000000000 : ℝ)*X 0 2+(3361541483/10000000000 : ℝ)*X 1 0+(2205599387/5000000000 : ℝ)*X 1 1+(2205599277/5000000000 : ℝ)*X 1 2+(3361541483/10000000000 : ℝ)*X 2 0+(2205599387/5000000000 : ℝ)*X 2 1+(2205599277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68767/100000 : ℝ) ≤ (-197740365771568317218880290783301/287562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18507297/100000000000000 : ℝ)*(lower1) + (684313/2500000000000 : ℝ)*(lower2) + (3406143/50000000000000 : ℝ)*(lower3) + (3391773/25000000000000 : ℝ)*(upper5) + (1022153422152431/100000000000000 : ℝ)*(major0) + (1022153422152431/100000000000000 : ℝ)*(major1) + (1022153422152431/100000000000000 : ℝ)*(major2) + (268937413/25000000000000 : ℝ)*(sp1) + (516947453/50000000000000 : ℝ)*(sp2) + (157798207289543/10000000000000 : ℝ)*(sp4) + (1577980997145779/100000000000000 : ℝ)*(sp5) + (63119241560021/4000000000000 : ℝ)*(sp6) + (489245873118439/100000000000000 : ℝ)*(sp7) + (66917989/20000000000000 : ℝ)*(sp15) + (15288943990887/3125000000000 : ℝ)*(f.failure) + (157798207289543/10000000000000 : ℝ)*(f.sum) + (174094606683281/46010000000000000000000000000 : ℝ)*base65 + (360386917402140983/575125000000000000000000000000000 : ℝ)*base67 + (2095849930246765983/575125000000000000000000000000000 : ℝ)*base69 + (1630438399746359017/575125000000000000000000000000000 : ℝ)*base72 + (52102890774991/46010000000000000000000000000 : ℝ)*base73 + (2867787135063734017/575125000000000000000000000000000 : ℝ)*base76 + (1111824709493609017/575125000000000000000000000000000 : ℝ)*base78 + (1112197767775609017/575125000000000000000000000000000 : ℝ)*base80 + (213467068338979/46010000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (272297/156250000000000000000 : ℝ)*base90 + (272297/156250000000000000000 : ℝ)*base92 + (272297/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3607/6250 : ℝ) ≤ (20745812251803465169472844315291/35945312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (186973/20000000000000 : ℝ)*(upper0) + (5923311/25000000000000 : ℝ)*(lower1) + (52064597/100000000000000 : ℝ)*(upper4) + (142617456589793/12500000000000 : ℝ)*(major0) + (142617456589793/12500000000000 : ℝ)*(major1) + (142617456589793/12500000000000 : ℝ)*(major2) + (343307364333287/20000000000000 : ℝ)*(sp0) + (1716537708810939/100000000000000 : ℝ)*(sp1) + (214567264303253/12500000000000 : ℝ)*(sp2) + (546101636584417/100000000000000 : ℝ)*(sp3) + (924194261/100000000000000 : ℝ)*(sp5) + (64822397/12500000000000 : ℝ)*(sp6) + (362782509/50000000000000 : ℝ)*(sp7) + (362267753/20000000000000 : ℝ)*(sp8) + (109220472429887/20000000000000 : ℝ)*(f.failure) + (4291346582513/250000000000 : ℝ)*(f.sum) + (63836310063739/11502500000000000000000000000 : ℝ)*base66 + (53567650812861897/8986328125000000000000000000000 : ℝ)*base68 + (250205170331619463/35945312500000000000000000000000 : ℝ)*base70 + (563676542061660801/71890625000000000000000000000000 : ℝ)*base72 + (24790695171337/5751250000000000000000000000 : ℝ)*base74 + (689872255612348301/71890625000000000000000000000000 : ℝ)*base76 + (20992749761501261/4493164062500000000000000000000 : ℝ)*base78 + (453228099968067051/71890625000000000000000000000000 : ℝ)*base80 + (66102513847873/23005000000000000000000000000 : ℝ)*base82 + (13456203/1000000000000000000000 : ℝ)*base89 + (13456203/1000000000000000000000 : ℝ)*base91 + (13456203/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2534/3125 : ℝ) ≤ (233186761029544849679288139672429/287562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24925369/50000000000000 : ℝ)*(upper2) + (7313827/20000000000000 : ℝ)*(upper3) + (14960711/50000000000000 : ℝ)*(upper4) + (1108277103935699/100000000000000 : ℝ)*(major0) + (1108277103935699/100000000000000 : ℝ)*(major1) + (1108277103935699/100000000000000 : ℝ)*(major2) + (846803071/100000000000000 : ℝ)*(sp0) + (24337145063/100000000000000 : ℝ)*(sp1) + (31427817/156250000000 : ℝ)*(sp2) + (136794931/2500000000000 : ℝ)*(sp3) + (331810883456943/20000000000000 : ℝ)*(sp8) + (829515463471361/50000000000000 : ℝ)*(sp9) + (829517575142453/50000000000000 : ℝ)*(sp10) + (530463201925707/100000000000000 : ℝ)*(sp11) + (530468673722947/100000000000000 : ℝ)*(f.failure) + (829527632043893/50000000000000 : ℝ)*(f.sum) + (258571496446711/46010000000000000000000000000 : ℝ)*base66 + (4565834580820792893/575125000000000000000000000000000 : ℝ)*base68 + (2429206151476332107/575125000000000000000000000000000 : ℝ)*base69 + (927870709892582107/575125000000000000000000000000000 : ℝ)*base71 + (104627386719561/46010000000000000000000000000 : ℝ)*base74 + (5921819162627957107/575125000000000000000000000000000 : ℝ)*base75 + (7903994529036082107/575125000000000000000000000000000 : ℝ)*base77 + (444310089447417893/575125000000000000000000000000000 : ℝ)*base80 + (66200386649519/46010000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (26397343/5000000000000000000000 : ℝ)*base89 + (26397343/5000000000000000000000 : ℝ)*base91 + (26397343/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-23187/25000 : ℝ) ≤ (-266701475676743344020176293804251/287562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215519/6250000000000 : ℝ)*(lower1) + (15543111/50000000000000 : ℝ)*(upper3) + (315381/20000000000000 : ℝ)*(upper5) + (1162435502065619/100000000000000 : ℝ)*(major0) + (1162435502065619/100000000000000 : ℝ)*(major1) + (1162435502065619/100000000000000 : ℝ)*(major2) + (173351037/50000000000000 : ℝ)*(sp0) + (5225993433/50000000000000 : ℝ)*(sp6) + (671424231/100000000000000 : ℝ)*(sp7) + (155287153/50000000000000 : ℝ)*(sp8) + (899697172127411/50000000000000 : ℝ)*(sp12) + (899697500765601/50000000000000 : ℝ)*(sp13) + (112461534346521/6250000000000 : ℝ)*(sp14) + (556390520705813/100000000000000 : ℝ)*(sp15) + (139097798032511/25000000000000 : ℝ)*(f.failure) + (899697500765601/50000000000000 : ℝ)*(f.sum) + (77021056394469/46010000000000000000000000000 : ℝ)*base65 + (3447974087003732667/575125000000000000000000000000000 : ℝ)*base67 + (1736829891445642333/575125000000000000000000000000000 : ℝ)*base70 + (823141681558357667/575125000000000000000000000000000 : ℝ)*base71 + (205762023648419/46010000000000000000000000000 : ℝ)*base73 + (336240880149642333/575125000000000000000000000000000 : ℝ)*base76 + (673525029268357667/575125000000000000000000000000000 : ℝ)*base77 + (2293833296213482667/575125000000000000000000000000000 : ℝ)*base79 + (247988406468311/46010000000000000000000000000 : ℝ)*base82 + (9174741/1250000000000000000000 : ℝ)*base90 + (9174741/1250000000000000000000 : ℝ)*base92 + (9174741/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1742_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4533/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (893/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68767/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3607/6250 : ℝ) else (2534/3125 : ℝ) ≤ X j i ∧ X j i ≤ (23187/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1742_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1742_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68767/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3607/6250 : ℝ) else (2534/3125 : ℝ) ≤ X j i ∧ X j i ≤ (23187/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1742_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1742_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68767/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3607/6250 : ℝ) else (2534/3125 : ℝ) ≤ X j i ∧ X j i ≤ (23187/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
