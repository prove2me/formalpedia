-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:04.495025+00:00
-- url     : https://prove2.me/submissions/6e742a8e-e5d6-4749-9a05-39c33301389b

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
theorem support_rectangle_w1550_s6_0 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453326607/2500000000 : ℝ)*x 0 + (2714165463/5000000000 : ℝ)*x 1 + (5219337049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453326607/2500000000 : ℝ)^4597 ≤ (11116128836221/100000000000000 : ℝ)^3573 := by
    have hnat : (453326607 : ℕ)^4597*100000000000000^3573 ≤ 11116128836221^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453326607 2500000000 11116128836221 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714165463/5000000000 : ℝ)^4597 ≤ (45564152895503/100000000000000 : ℝ)^3573 := by
    have hnat : (2714165463 : ℕ)^4597*100000000000000^3573 ≤ 45564152895503^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714165463 5000000000 45564152895503 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219337049/10000000000 : ℝ)^4597 ≤ (43319718263381/100000000000000 : ℝ)^3573 := by
    have hnat : (5219337049 : ℕ)^4597*100000000000000^3573 ≤ 43319718263381^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219337049 10000000000 43319718263381 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453326607/2500000000 : ℝ), (2714165463/5000000000 : ℝ), (5219337049/10000000000 : ℝ)] ![(11116128836221/100000000000000 : ℝ), (45564152895503/100000000000000 : ℝ), (43319718263381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453326607/2500000000 : ℝ)|^4597 ≤ (11116128836221/100000000000000 : ℝ)^3573
        have hw : |(-453326607/2500000000 : ℝ)|=(453326607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714165463/5000000000 : ℝ)|^4597 ≤ (45564152895503/100000000000000 : ℝ)^3573
        have hw : |(2714165463/5000000000 : ℝ)|=(2714165463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219337049/10000000000 : ℝ)|^4597 ≤ (43319718263381/100000000000000 : ℝ)^3573
        have hw : |(5219337049/10000000000 : ℝ)|=(5219337049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_1 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534939879/1000000000 : ℝ)*x 0 + (-960131779/5000000000 : ℝ)*x 1 + (5219337811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534939879/1000000000 : ℝ)^4597 ≤ (44713517771291/100000000000000 : ℝ)^3573 := by
    have hnat : (534939879 : ℕ)^4597*100000000000000^3573 ≤ 44713517771291^3573*1000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534939879 1000000000 44713517771291 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960131779/5000000000 : ℝ)^4597 ≤ (5983377909253/50000000000000 : ℝ)^3573 := by
    have hnat : (960131779 : ℕ)^4597*50000000000000^3573 ≤ 5983377909253^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960131779 5000000000 5983377909253 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219337811/10000000000 : ℝ)^4597 ≤ (21659863200213/50000000000000 : ℝ)^3573 := by
    have hnat : (5219337811 : ℕ)^4597*50000000000000^3573 ≤ 21659863200213^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219337811 10000000000 21659863200213 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534939879/1000000000 : ℝ), (-960131779/5000000000 : ℝ), (5219337811/10000000000 : ℝ)] ![(44713517771291/100000000000000 : ℝ), (5983377909253/50000000000000 : ℝ), (21659863200213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534939879/1000000000 : ℝ)|^4597 ≤ (44713517771291/100000000000000 : ℝ)^3573
        have hw : |(534939879/1000000000 : ℝ)|=(534939879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960131779/5000000000 : ℝ)|^4597 ≤ (5983377909253/50000000000000 : ℝ)^3573
        have hw : |(-960131779/5000000000 : ℝ)|=(960131779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219337811/10000000000 : ℝ)|^4597 ≤ (21659863200213/50000000000000 : ℝ)^3573
        have hw : |(5219337811/10000000000 : ℝ)|=(5219337811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_2 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349399143/10000000000 : ℝ)*x 0 + (652417167/1250000000 : ℝ)*x 1 + (-480065929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349399143/10000000000 : ℝ)^4597 ≤ (44713521567499/100000000000000 : ℝ)^3573 := by
    have hnat : (5349399143 : ℕ)^4597*100000000000000^3573 ≤ 44713521567499^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349399143 10000000000 44713521567499 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652417167/1250000000 : ℝ)^4597 ≤ (43319721328121/100000000000000 : ℝ)^3573 := by
    have hnat : (652417167 : ℕ)^4597*100000000000000^3573 ≤ 43319721328121^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652417167 1250000000 43319721328121 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480065929/2500000000 : ℝ)^4597 ≤ (2991689271331/25000000000000 : ℝ)^3573 := by
    have hnat : (480065929 : ℕ)^4597*25000000000000^3573 ≤ 2991689271331^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480065929 2500000000 2991689271331 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349399143/10000000000 : ℝ), (652417167/1250000000 : ℝ), (-480065929/2500000000 : ℝ)] ![(44713521567499/100000000000000 : ℝ), (43319721328121/100000000000000 : ℝ), (2991689271331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349399143/10000000000 : ℝ)|^4597 ≤ (44713521567499/100000000000000 : ℝ)^3573
        have hw : |(5349399143/10000000000 : ℝ)|=(5349399143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652417167/1250000000 : ℝ)|^4597 ≤ (43319721328121/100000000000000 : ℝ)^3573
        have hw : |(652417167/1250000000 : ℝ)|=(652417167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-480065929/2500000000 : ℝ)|^4597 ≤ (2991689271331/25000000000000 : ℝ)^3573
        have hw : |(-480065929/2500000000 : ℝ)|=(480065929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_3 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126198859/5000000000 : ℝ)*x 0 + (50185177/125000000 : ℝ)*x 1 + (4501440639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126198859/5000000000 : ℝ)^4597 ≤ (6656295700469/20000000000000 : ℝ)^3573 := by
    have hnat : (2126198859 : ℕ)^4597*20000000000000^3573 ≤ 6656295700469^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126198859 5000000000 6656295700469 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50185177/125000000 : ℝ)^4597 ≤ (1545426613507/5000000000000 : ℝ)^3573 := by
    have hnat : (50185177 : ℕ)^4597*5000000000000^3573 ≤ 1545426613507^3573*125000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50185177 125000000 1545426613507 5000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501440639/10000000000 : ℝ)^4597 ≤ (35809989213929/100000000000000 : ℝ)^3573 := by
    have hnat : (4501440639 : ℕ)^4597*100000000000000^3573 ≤ 35809989213929^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501440639 10000000000 35809989213929 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126198859/5000000000 : ℝ), (50185177/125000000 : ℝ), (4501440639/10000000000 : ℝ)] ![(6656295700469/20000000000000 : ℝ), (1545426613507/5000000000000 : ℝ), (35809989213929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126198859/5000000000 : ℝ)|^4597 ≤ (6656295700469/20000000000000 : ℝ)^3573
        have hw : |(2126198859/5000000000 : ℝ)|=(2126198859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50185177/125000000 : ℝ)|^4597 ≤ (1545426613507/5000000000000 : ℝ)^3573
        have hw : |(50185177/125000000 : ℝ)|=(50185177/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501440639/10000000000 : ℝ)|^4597 ≤ (35809989213929/100000000000000 : ℝ)^3573
        have hw : |(4501440639/10000000000 : ℝ)|=(4501440639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_4 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-362666807/2000000000 : ℝ)*x 0 + (1305105319/2500000000 : ℝ)*x 1 + (5427238603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362666807/2000000000 : ℝ)^4597 ≤ (1111634657913/10000000000000 : ℝ)^3573 := by
    have hnat : (362666807 : ℕ)^4597*10000000000000^3573 ≤ 1111634657913^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362666807 2000000000 1111634657913 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305105319/2500000000 : ℝ)^4597 ≤ (1083282414161/2500000000000 : ℝ)^3573 := by
    have hnat : (1305105319 : ℕ)^4597*2500000000000^3573 ≤ 1083282414161^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305105319 2500000000 1083282414161 2500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427238603/10000000000 : ℝ)^4597 ≤ (45552356834033/100000000000000 : ℝ)^3573 := by
    have hnat : (5427238603 : ℕ)^4597*100000000000000^3573 ≤ 45552356834033^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427238603 10000000000 45552356834033 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-362666807/2000000000 : ℝ), (1305105319/2500000000 : ℝ), (5427238603/10000000000 : ℝ)] ![(1111634657913/10000000000000 : ℝ), (1083282414161/2500000000000 : ℝ), (45552356834033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-362666807/2000000000 : ℝ)|^4597 ≤ (1111634657913/10000000000000 : ℝ)^3573
        have hw : |(-362666807/2000000000 : ℝ)|=(362666807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305105319/2500000000 : ℝ)|^4597 ≤ (1083282414161/2500000000000 : ℝ)^3573
        have hw : |(1305105319/2500000000 : ℝ)|=(1305105319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427238603/10000000000 : ℝ)|^4597 ≤ (45552356834033/100000000000000 : ℝ)^3573
        have hw : |(5427238603/10000000000 : ℝ)|=(5427238603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_5 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661780377/1250000000 : ℝ)*x 0 + (5427238473/10000000000 : ℝ)*x 1 + (-1712362681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661780377/1250000000 : ℝ)^4597 ≤ (44121243845087/100000000000000 : ℝ)^3573 := by
    have hnat : (661780377 : ℕ)^4597*100000000000000^3573 ≤ 44121243845087^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661780377 1250000000 44121243845087 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427238473/10000000000 : ℝ)^4597 ≤ (9110471086039/20000000000000 : ℝ)^3573 := by
    have hnat : (5427238473 : ℕ)^4597*20000000000000^3573 ≤ 9110471086039^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427238473 10000000000 9110471086039 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1712362681/10000000000 : ℝ)^4597 ≤ (516320035483/5000000000000 : ℝ)^3573 := by
    have hnat : (1712362681 : ℕ)^4597*5000000000000^3573 ≤ 516320035483^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712362681 10000000000 516320035483 5000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661780377/1250000000 : ℝ), (5427238473/10000000000 : ℝ), (-1712362681/10000000000 : ℝ)] ![(44121243845087/100000000000000 : ℝ), (9110471086039/20000000000000 : ℝ), (516320035483/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661780377/1250000000 : ℝ)|^4597 ≤ (44121243845087/100000000000000 : ℝ)^3573
        have hw : |(661780377/1250000000 : ℝ)|=(661780377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427238473/10000000000 : ℝ)|^4597 ≤ (9110471086039/20000000000000 : ℝ)^3573
        have hw : |(5427238473/10000000000 : ℝ)|=(5427238473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1712362681/10000000000 : ℝ)|^4597 ≤ (516320035483/5000000000000 : ℝ)^3573
        have hw : |(-1712362681/10000000000 : ℝ)|=(1712362681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_s6_6 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252462453/10000000000 : ℝ)*x 0 + (4498916169/10000000000 : ℝ)*x 1 + (4017356523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252462453/10000000000 : ℝ)^4597 ≤ (16641065178163/50000000000000 : ℝ)^3573 := by
    have hnat : (4252462453 : ℕ)^4597*50000000000000^3573 ≤ 16641065178163^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252462453 10000000000 16641065178163 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498916169/10000000000 : ℝ)^4597 ≤ (17892076482593/50000000000000 : ℝ)^3573 := by
    have hnat : (4498916169 : ℕ)^4597*50000000000000^3573 ≤ 17892076482593^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498916169 10000000000 17892076482593 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017356523/10000000000 : ℝ)^4597 ≤ (7733429164271/25000000000000 : ℝ)^3573 := by
    have hnat : (4017356523 : ℕ)^4597*25000000000000^3573 ≤ 7733429164271^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017356523 10000000000 7733429164271 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252462453/10000000000 : ℝ), (4498916169/10000000000 : ℝ), (4017356523/10000000000 : ℝ)] ![(16641065178163/50000000000000 : ℝ), (17892076482593/50000000000000 : ℝ), (7733429164271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252462453/10000000000 : ℝ)|^4597 ≤ (16641065178163/50000000000000 : ℝ)^3573
        have hw : |(4252462453/10000000000 : ℝ)|=(4252462453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498916169/10000000000 : ℝ)|^4597 ≤ (17892076482593/50000000000000 : ℝ)^3573
        have hw : |(4498916169/10000000000 : ℝ)|=(4498916169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017356523/10000000000 : ℝ)|^4597 ≤ (7733429164271/25000000000000 : ℝ)^3573
        have hw : |(4017356523/10000000000 : ℝ)|=(4017356523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1550_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2211/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5527/50000 : ℝ) ^ (4595/1024 : ℝ) ≤ (1020963899696153/20000000000000000000 : ℝ) := by
    have hpowers : (5527/50000 : ℝ)^4595 ≤ (1020963899696153/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5527 : ℕ)^4595*20000000000000000000^1024 ≤ 1020963899696153^1024*50000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5527 50000 1020963899696153 20000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5527/50000 : ℝ)) (X := (1020963899696153/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4595/1024 : ℝ) ≤ (2895974856976871/12500000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4595 ≤ (2895974856976871/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4595*12500000000000000000^1024 ≤ 2895974856976871^1024*20000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 2895974856976871 12500000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (2895974856976871/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001020963899696153/10000000000000000000 : ℝ) ≤ (5000113756861803/5000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (10001020963899696153/10000000000000000000 : ℝ)^1024 ≤ (5000113756861803/5000000000000000 : ℝ)^4595 := by
      have hnat : (10001020963899696153 : ℕ)^1024*5000000000000000^4595 ≤ 5000113756861803^4595*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001020963899696153 10000000000000000000 5000113756861803 5000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000113756861803/5000000000000000 : ℝ)) (X := (10001020963899696153/10000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028272618354295733/100000000000000000000 : ℝ) ≤ (10000629988708317/10000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (100028272618354295733/100000000000000000000 : ℝ)^1024 ≤ (10000629988708317/10000000000000000 : ℝ)^4595 := by
      have hnat : (100028272618354295733 : ℕ)^1024*10000000000000000^4595 ≤ 10000629988708317^4595*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028272618354295733 100000000000000000000 10000629988708317 10000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000629988708317/10000000000000000 : ℝ)) (X := (100028272618354295733/100000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252895974856976871/6250000000000000000 : ℝ) ≤ (2500258115923257/2500000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (6252895974856976871/6250000000000000000 : ℝ)^1024 ≤ (2500258115923257/2500000000000000 : ℝ)^4595 := by
      have hnat : (6252895974856976871 : ℕ)^1024*2500000000000000^4595 ≤ 2500258115923257^4595*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252895974856976871 6250000000000000000 2500258115923257 2500000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500258115923257/2500000000000000 : ℝ)) (X := (6252895974856976871/6250000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1020963899696153/20000000000000000000 : ℝ) ≤ ((7383685032724551233/7385000000000000000 : ℝ)+2*(134158328237/147700000000000 : ℝ)*(5527/50000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (7383685032724551233/7385000000000000000 : ℝ)+2*(134158328237/147700000000000 : ℝ)*(5527/50000 : ℝ)=(5000113756861803/5000000000000000 : ℝ) by norm_num, show 1+2*(1020963899696153/20000000000000000000 : ℝ)=(10001020963899696153/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2895974856976871/12500000000000000000 : ℝ)+(1020963899696153/20000000000000000000 : ℝ) ≤ ((7383685032724551233/7385000000000000000 : ℝ)+(134158328237/147700000000000 : ℝ)*((3097/20000 : ℝ)+(5527/50000 : ℝ)))^(4595/1024 : ℝ) := by
    rw [show (7383685032724551233/7385000000000000000 : ℝ)+(134158328237/147700000000000 : ℝ)*((3097/20000 : ℝ)+(5527/50000 : ℝ))=(10000629988708317/10000000000000000 : ℝ) by norm_num, show 1+(2895974856976871/12500000000000000000 : ℝ)+(1020963899696153/20000000000000000000 : ℝ)=(100028272618354295733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2895974856976871/12500000000000000000 : ℝ) ≤ ((7383685032724551233/7385000000000000000 : ℝ)+2*(134158328237/147700000000000 : ℝ)*(3097/20000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (7383685032724551233/7385000000000000000 : ℝ)+2*(134158328237/147700000000000 : ℝ)*(3097/20000 : ℝ)=(2500258115923257/2500000000000000 : ℝ) by norm_num, show 1+2*(2895974856976871/12500000000000000000 : ℝ)=(6252895974856976871/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7383685032724551233/7385000000000000000 : ℝ)*(X 1 0+X 2 0)+(134158328237/147700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7383685032724551233/7385000000000000000 : ℝ)) (alpha := (134158328237/147700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7383685032724551233/7385000000000000000 : ℝ)*(X 0 1+X 2 1)+(134158328237/147700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7383685032724551233/7385000000000000000 : ℝ)) (alpha := (134158328237/147700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7383685032724551233/7385000000000000000 : ℝ)*(X 0 2+X 1 2)+(134158328237/147700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7383685032724551233/7385000000000000000 : ℝ)) (alpha := (134158328237/147700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-453326607/2500000000 : ℝ)*X 0 0+(2714165463/5000000000 : ℝ)*X 0 1+(5219337049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534939879/1000000000 : ℝ)*X 1 0+(-960131779/5000000000 : ℝ)*X 1 1+(5219337811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349399143/10000000000 : ℝ)*X 2 0+(652417167/1250000000 : ℝ)*X 2 1+(-480065929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2126198859/5000000000 : ℝ)*X 0 0+(50185177/125000000 : ℝ)*X 0 1+(4501440639/10000000000 : ℝ)*X 0 2+(2126198859/5000000000 : ℝ)*X 1 0+(50185177/125000000 : ℝ)*X 1 1+(4501440639/10000000000 : ℝ)*X 1 2+(2126198859/5000000000 : ℝ)*X 2 0+(50185177/125000000 : ℝ)*X 2 1+(4501440639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-362666807/2000000000 : ℝ)*X 0 0+(1305105319/2500000000 : ℝ)*X 0 1+(5427238603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661780377/1250000000 : ℝ)*X 2 0+(5427238473/10000000000 : ℝ)*X 2 1+(-1712362681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4252462453/10000000000 : ℝ)*X 0 0+(4498916169/10000000000 : ℝ)*X 0 1+(4017356523/10000000000 : ℝ)*X 0 2+(4252462453/10000000000 : ℝ)*X 1 0+(4498916169/10000000000 : ℝ)*X 1 1+(4017356523/10000000000 : ℝ)*X 1 2+(4252462453/10000000000 : ℝ)*X 2 0+(4498916169/10000000000 : ℝ)*X 2 1+(4017356523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (494874236668459285071525807/92312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73751303/100000000000000 : ℝ)*(base23) + (1228969/1562500000000 : ℝ)*(lower2) + (535643/2500000000000 : ℝ)*(upper4) + (11250767/50000000000000 : ℝ)*(lower5) + (1709957728995793/50000000000000 : ℝ)*(major0) + (1709957728995793/50000000000000 : ℝ)*(major1) + (1709957728995793/50000000000000 : ℝ)*(major2) + (956968743167401/20000000000000 : ℝ)*(sp0) + (1196215313323153/25000000000000 : ℝ)*(sp1) + (2392427927024721/50000000000000 : ℝ)*(sp2) + (205496609388931/10000000000000 : ℝ)*(sp3) + (17537455607/100000000000000 : ℝ)*(sp4) + (5325491867/100000000000000 : ℝ)*(sp5) + (847526491/25000000000000 : ℝ)*(sp6) + (1027484741997637/50000000000000 : ℝ)*(f.failure) + (1196215313323153/25000000000000 : ℝ)*(f.sum) + (159877611928387/7385000000000000000000000000 : ℝ)*base65 + (2101677198334487231/369250000000000000000000000000000 : ℝ)*base68 + (1524832946696987231/369250000000000000000000000000000 : ℝ)*base70 + (928839897408987231/369250000000000000000000000000000 : ℝ)*base72 + (8093407606909/3692500000000000000000000000 : ℝ)*base74 + (1933835318317487231/369250000000000000000000000000000 : ℝ)*base76 + (779382118970487231/369250000000000000000000000000000 : ℝ)*base78 + (1684407574326262769/369250000000000000000000000000000 : ℝ)*base79 + (23792012683127/7385000000000000000000000000 : ℝ)*base81 + (4902509/1000000000000000000000 : ℝ)*base90 + (4902509/1000000000000000000000 : ℝ)*base92 + (4902509/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1550_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2211/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1550_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1550_box_0 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-401558439/2500000000 : ℝ)*x 0 + (5398736181/10000000000 : ℝ)*x 1 + (5398737317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401558439/2500000000 : ℝ)^4597 ≤ (1902078240221/20000000000000 : ℝ)^3573 := by
    have hnat : (401558439 : ℕ)^4597*20000000000000^3573 ≤ 1902078240221^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401558439 2500000000 1902078240221 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398736181/10000000000 : ℝ)^4597 ≤ (11311199567269/25000000000000 : ℝ)^3573 := by
    have hnat : (5398736181 : ℕ)^4597*25000000000000^3573 ≤ 11311199567269^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398736181 10000000000 11311199567269 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398737317/10000000000 : ℝ)^4597 ≤ (11311202629489/25000000000000 : ℝ)^3573 := by
    have hnat : (5398737317 : ℕ)^4597*25000000000000^3573 ≤ 11311202629489^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398737317 10000000000 11311202629489 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401558439/2500000000 : ℝ), (5398736181/10000000000 : ℝ), (5398737317/10000000000 : ℝ)] ![(1902078240221/20000000000000 : ℝ), (11311199567269/25000000000000 : ℝ), (11311202629489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401558439/2500000000 : ℝ)|^4597 ≤ (1902078240221/20000000000000 : ℝ)^3573
        have hw : |(-401558439/2500000000 : ℝ)|=(401558439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398736181/10000000000 : ℝ)|^4597 ≤ (11311199567269/25000000000000 : ℝ)^3573
        have hw : |(5398736181/10000000000 : ℝ)|=(5398736181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398737317/10000000000 : ℝ)|^4597 ≤ (11311202629489/25000000000000 : ℝ)^3573
        have hw : |(5398737317/10000000000 : ℝ)|=(5398737317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_1 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271100031/10000000000 : ℝ)*x 0 + (-1783543617/10000000000 : ℝ)*x 1 + (269936853/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271100031/10000000000 : ℝ)^4597 ≤ (10968313724431/25000000000000 : ℝ)^3573 := by
    have hnat : (5271100031 : ℕ)^4597*25000000000000^3573 ≤ 10968313724431^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271100031 10000000000 10968313724431 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783543617/10000000000 : ℝ)^4597 ≤ (10881937345797/100000000000000 : ℝ)^3573 := by
    have hnat : (1783543617 : ℕ)^4597*100000000000000^3573 ≤ 10881937345797^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783543617 10000000000 10881937345797 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269936853/500000000 : ℝ)^4597 ≤ (22622403873431/50000000000000 : ℝ)^3573 := by
    have hnat : (269936853 : ℕ)^4597*50000000000000^3573 ≤ 22622403873431^3573*500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269936853 500000000 22622403873431 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271100031/10000000000 : ℝ), (-1783543617/10000000000 : ℝ), (269936853/500000000 : ℝ)] ![(10968313724431/25000000000000 : ℝ), (10881937345797/100000000000000 : ℝ), (22622403873431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271100031/10000000000 : ℝ)|^4597 ≤ (10968313724431/25000000000000 : ℝ)^3573
        have hw : |(5271100031/10000000000 : ℝ)|=(5271100031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783543617/10000000000 : ℝ)|^4597 ≤ (10881937345797/100000000000000 : ℝ)^3573
        have hw : |(-1783543617/10000000000 : ℝ)|=(1783543617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269936853/500000000 : ℝ)|^4597 ≤ (22622403873431/50000000000000 : ℝ)^3573
        have hw : |(269936853/500000000 : ℝ)|=(269936853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_2 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527109991/1000000000 : ℝ)*x 0 + (1079747481/2000000000 : ℝ)*x 1 + (-1783543307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527109991/1000000000 : ℝ)^4597 ≤ (43873253601961/100000000000000 : ℝ)^3573 := by
    have hnat : (527109991 : ℕ)^4597*100000000000000^3573 ≤ 43873253601961^3573*1000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527109991 1000000000 43873253601961 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079747481/2000000000 : ℝ)^4597 ≤ (45244811466813/100000000000000 : ℝ)^3573 := by
    have hnat : (1079747481 : ℕ)^4597*100000000000000^3573 ≤ 45244811466813^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079747481 2000000000 45244811466813 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783543307/10000000000 : ℝ)^4597 ≤ (10881934912329/100000000000000 : ℝ)^3573 := by
    have hnat : (1783543307 : ℕ)^4597*100000000000000^3573 ≤ 10881934912329^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783543307 10000000000 10881934912329 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527109991/1000000000 : ℝ), (1079747481/2000000000 : ℝ), (-1783543307/10000000000 : ℝ)] ![(43873253601961/100000000000000 : ℝ), (45244811466813/100000000000000 : ℝ), (10881934912329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527109991/1000000000 : ℝ)|^4597 ≤ (43873253601961/100000000000000 : ℝ)^3573
        have hw : |(527109991/1000000000 : ℝ)|=(527109991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079747481/2000000000 : ℝ)|^4597 ≤ (45244811466813/100000000000000 : ℝ)^3573
        have hw : |(1079747481/2000000000 : ℝ)|=(1079747481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783543307/10000000000 : ℝ)|^4597 ≤ (10881934912329/100000000000000 : ℝ)^3573
        have hw : |(-1783543307/10000000000 : ℝ)|=(1783543307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_3 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (890769791/2000000000 : ℝ)*x 0 + (1039605479/2500000000 : ℝ)*x 1 + (4158420459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890769791/2000000000 : ℝ)^4597 ≤ (17661810548671/50000000000000 : ℝ)^3573 := by
    have hnat : (890769791 : ℕ)^4597*50000000000000^3573 ≤ 17661810548671^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890769791 2000000000 17661810548671 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039605479/2500000000 : ℝ)^4597 ≤ (8084549182887/25000000000000 : ℝ)^3573 := by
    have hnat : (1039605479 : ℕ)^4597*25000000000000^3573 ≤ 8084549182887^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039605479 2500000000 8084549182887 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158420459/10000000000 : ℝ)^4597 ≤ (32338182153873/100000000000000 : ℝ)^3573 := by
    have hnat : (4158420459 : ℕ)^4597*100000000000000^3573 ≤ 32338182153873^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158420459 10000000000 32338182153873 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(890769791/2000000000 : ℝ), (1039605479/2500000000 : ℝ), (4158420459/10000000000 : ℝ)] ![(17661810548671/50000000000000 : ℝ), (8084549182887/25000000000000 : ℝ), (32338182153873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(890769791/2000000000 : ℝ)|^4597 ≤ (17661810548671/50000000000000 : ℝ)^3573
        have hw : |(890769791/2000000000 : ℝ)|=(890769791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039605479/2500000000 : ℝ)|^4597 ≤ (8084549182887/25000000000000 : ℝ)^3573
        have hw : |(1039605479/2500000000 : ℝ)|=(1039605479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158420459/10000000000 : ℝ)|^4597 ≤ (32338182153873/100000000000000 : ℝ)^3573
        have hw : |(4158420459/10000000000 : ℝ)|=(4158420459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_4 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025784333/10000000000 : ℝ)*x 0 + (5244659139/10000000000 : ℝ)*x 1 + (1048931851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025784333/10000000000 : ℝ)^4597 ≤ (2563876182051/20000000000000 : ℝ)^3573 := by
    have hnat : (2025784333 : ℕ)^4597*20000000000000^3573 ≤ 2563876182051^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025784333 10000000000 2563876182051 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244659139/10000000000 : ℝ)^4597 ≤ (21795154458907/50000000000000 : ℝ)^3573 := by
    have hnat : (5244659139 : ℕ)^4597*50000000000000^3573 ≤ 21795154458907^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244659139 10000000000 21795154458907 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048931851/2000000000 : ℝ)^4597 ≤ (10897577539561/25000000000000 : ℝ)^3573 := by
    have hnat : (1048931851 : ℕ)^4597*25000000000000^3573 ≤ 10897577539561^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048931851 2000000000 10897577539561 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025784333/10000000000 : ℝ), (5244659139/10000000000 : ℝ), (1048931851/2000000000 : ℝ)] ![(2563876182051/20000000000000 : ℝ), (21795154458907/50000000000000 : ℝ), (10897577539561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025784333/10000000000 : ℝ)|^4597 ≤ (2563876182051/20000000000000 : ℝ)^3573
        have hw : |(-2025784333/10000000000 : ℝ)|=(2025784333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244659139/10000000000 : ℝ)|^4597 ≤ (21795154458907/50000000000000 : ℝ)^3573
        have hw : |(5244659139/10000000000 : ℝ)|=(5244659139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048931851/2000000000 : ℝ)|^4597 ≤ (10897577539561/25000000000000 : ℝ)^3573
        have hw : |(1048931851/2000000000 : ℝ)|=(1048931851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_5 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378061767/10000000000 : ℝ)*x 0 + (-230955431/1250000000 : ℝ)*x 1 + (8194781/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378061767/10000000000 : ℝ)^4597 ≤ (9004399914781/20000000000000 : ℝ)^3573 := by
    have hnat : (5378061767 : ℕ)^4597*20000000000000^3573 ≤ 9004399914781^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378061767 10000000000 9004399914781 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230955431/1250000000 : ℝ)^4597 ≤ (11387684001381/100000000000000 : ℝ)^3573 := by
    have hnat : (230955431 : ℕ)^4597*100000000000000^3573 ≤ 11387684001381^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230955431 1250000000 11387684001381 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8194781/15625000 : ℝ)^4597 ≤ (43590316413859/100000000000000 : ℝ)^3573 := by
    have hnat : (8194781 : ℕ)^4597*100000000000000^3573 ≤ 43590316413859^3573*15625000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8194781 15625000 43590316413859 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378061767/10000000000 : ℝ), (-230955431/1250000000 : ℝ), (8194781/15625000 : ℝ)] ![(9004399914781/20000000000000 : ℝ), (11387684001381/100000000000000 : ℝ), (43590316413859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378061767/10000000000 : ℝ)|^4597 ≤ (9004399914781/20000000000000 : ℝ)^3573
        have hw : |(5378061767/10000000000 : ℝ)|=(5378061767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-230955431/1250000000 : ℝ)|^4597 ≤ (11387684001381/100000000000000 : ℝ)^3573
        have hw : |(-230955431/1250000000 : ℝ)|=(230955431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8194781/15625000 : ℝ)|^4597 ≤ (43590316413859/100000000000000 : ℝ)^3573
        have hw : |(8194781/15625000 : ℝ)|=(8194781/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_6 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378063681/10000000000 : ℝ)*x 0 + (5244658703/10000000000 : ℝ)*x 1 + (-1847642381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378063681/10000000000 : ℝ)^4597 ≤ (45022020188863/100000000000000 : ℝ)^3573 := by
    have hnat : (5378063681 : ℕ)^4597*100000000000000^3573 ≤ 45022020188863^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378063681 10000000000 45022020188863 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244658703/10000000000 : ℝ)^4597 ≤ (43590304255509/100000000000000 : ℝ)^3573 := by
    have hnat : (5244658703 : ℕ)^4597*100000000000000^3573 ≤ 43590304255509^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244658703 10000000000 43590304255509 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1847642381/10000000000 : ℝ)^4597 ≤ (11387675540353/100000000000000 : ℝ)^3573 := by
    have hnat : (1847642381 : ℕ)^4597*100000000000000^3573 ≤ 11387675540353^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847642381 10000000000 11387675540353 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378063681/10000000000 : ℝ), (5244658703/10000000000 : ℝ), (-1847642381/10000000000 : ℝ)] ![(45022020188863/100000000000000 : ℝ), (43590304255509/100000000000000 : ℝ), (11387675540353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378063681/10000000000 : ℝ)|^4597 ≤ (45022020188863/100000000000000 : ℝ)^3573
        have hw : |(5378063681/10000000000 : ℝ)|=(5378063681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244658703/10000000000 : ℝ)|^4597 ≤ (43590304255509/100000000000000 : ℝ)^3573
        have hw : |(5244658703/10000000000 : ℝ)|=(5244658703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1847642381/10000000000 : ℝ)|^4597 ≤ (11387675540353/100000000000000 : ℝ)^3573
        have hw : |(-1847642381/10000000000 : ℝ)|=(1847642381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_7 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2024174337/5000000000 : ℝ)*x 0 + (272565117/625000000 : ℝ)*x 1 + (2180520741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024174337/5000000000 : ℝ)^4597 ≤ (31241088367507/100000000000000 : ℝ)^3573 := by
    have hnat : (2024174337 : ℕ)^4597*100000000000000^3573 ≤ 31241088367507^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024174337 5000000000 31241088367507 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272565117/625000000 : ℝ)^4597 ≤ (3437945779069/10000000000000 : ℝ)^3573 := by
    have hnat : (272565117 : ℕ)^4597*10000000000000^3573 ≤ 3437945779069^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272565117 625000000 3437945779069 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180520741/5000000000 : ℝ)^4597 ≤ (34379453835067/100000000000000 : ℝ)^3573 := by
    have hnat : (2180520741 : ℕ)^4597*100000000000000^3573 ≤ 34379453835067^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180520741 5000000000 34379453835067 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2024174337/5000000000 : ℝ), (272565117/625000000 : ℝ), (2180520741/5000000000 : ℝ)] ![(31241088367507/100000000000000 : ℝ), (3437945779069/10000000000000 : ℝ), (34379453835067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2024174337/5000000000 : ℝ)|^4597 ≤ (31241088367507/100000000000000 : ℝ)^3573
        have hw : |(2024174337/5000000000 : ℝ)|=(2024174337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272565117/625000000 : ℝ)|^4597 ≤ (3437945779069/10000000000000 : ℝ)^3573
        have hw : |(272565117/625000000 : ℝ)|=(272565117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180520741/5000000000 : ℝ)|^4597 ≤ (34379453835067/100000000000000 : ℝ)^3573
        have hw : |(2180520741/5000000000 : ℝ)|=(2180520741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_8 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936940017/10000000000 : ℝ)*x 0 + (5136313803/10000000000 : ℝ)*x 1 + (1354768053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936940017/10000000000 : ℝ)^4597 ≤ (3025157739091/25000000000000 : ℝ)^3573 := by
    have hnat : (1936940017 : ℕ)^4597*25000000000000^3573 ≤ 3025157739091^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936940017 10000000000 3025157739091 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136313803/10000000000 : ℝ)^4597 ≤ (1326099374291/3125000000000 : ℝ)^3573 := by
    have hnat : (5136313803 : ℕ)^4597*3125000000000^3573 ≤ 1326099374291^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136313803 10000000000 1326099374291 3125000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354768053/2500000000 : ℝ)^4597 ≤ (45464189053607/100000000000000 : ℝ)^3573 := by
    have hnat : (1354768053 : ℕ)^4597*100000000000000^3573 ≤ 45464189053607^3573*2500000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354768053 2500000000 45464189053607 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936940017/10000000000 : ℝ), (5136313803/10000000000 : ℝ), (1354768053/2500000000 : ℝ)] ![(3025157739091/25000000000000 : ℝ), (1326099374291/3125000000000 : ℝ), (45464189053607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936940017/10000000000 : ℝ)|^4597 ≤ (3025157739091/25000000000000 : ℝ)^3573
        have hw : |(-1936940017/10000000000 : ℝ)|=(1936940017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136313803/10000000000 : ℝ)|^4597 ≤ (1326099374291/3125000000000 : ℝ)^3573
        have hw : |(5136313803/10000000000 : ℝ)|=(5136313803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354768053/2500000000 : ℝ)|^4597 ≤ (45464189053607/100000000000000 : ℝ)^3573
        have hw : |(1354768053/2500000000 : ℝ)|=(1354768053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_9 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628489459/5000000000 : ℝ)*x 0 + (-1774846771/10000000000 : ℝ)*x 1 + (677384051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628489459/5000000000 : ℝ)^4597 ≤ (8744418612611/20000000000000 : ℝ)^3573 := by
    have hnat : (2628489459 : ℕ)^4597*20000000000000^3573 ≤ 8744418612611^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628489459 5000000000 8744418612611 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774846771/10000000000 : ℝ)^4597 ≤ (10813715755889/100000000000000 : ℝ)^3573 := by
    have hnat : (1774846771 : ℕ)^4597*100000000000000^3573 ≤ 10813715755889^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774846771 10000000000 10813715755889 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677384051/1250000000 : ℝ)^4597 ≤ (45464191169249/100000000000000 : ℝ)^3573 := by
    have hnat : (677384051 : ℕ)^4597*100000000000000^3573 ≤ 45464191169249^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677384051 1250000000 45464191169249 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628489459/5000000000 : ℝ), (-1774846771/10000000000 : ℝ), (677384051/1250000000 : ℝ)] ![(8744418612611/20000000000000 : ℝ), (10813715755889/100000000000000 : ℝ), (45464191169249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628489459/5000000000 : ℝ)|^4597 ≤ (8744418612611/20000000000000 : ℝ)^3573
        have hw : |(2628489459/5000000000 : ℝ)|=(2628489459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1774846771/10000000000 : ℝ)|^4597 ≤ (10813715755889/100000000000000 : ℝ)^3573
        have hw : |(-1774846771/10000000000 : ℝ)|=(1774846771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677384051/1250000000 : ℝ)|^4597 ≤ (45464191169249/100000000000000 : ℝ)^3573
        have hw : |(677384051/1250000000 : ℝ)|=(677384051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_10 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328561181/625000000 : ℝ)*x 0 + (5419072431/10000000000 : ℝ)*x 1 + (-1774846769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328561181/625000000 : ℝ)^4597 ≤ (43722092827643/100000000000000 : ℝ)^3573 := by
    have hnat : (328561181 : ℕ)^4597*100000000000000^3573 ≤ 43722092827643^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328561181 625000000 43722092827643 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419072431/10000000000 : ℝ)^4597 ≤ (45464191417513/100000000000000 : ℝ)^3573 := by
    have hnat : (5419072431 : ℕ)^4597*100000000000000^3573 ≤ 45464191417513^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419072431 10000000000 45464191417513 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1774846769/10000000000 : ℝ)^4597 ≤ (10813715740211/100000000000000 : ℝ)^3573 := by
    have hnat : (1774846769 : ℕ)^4597*100000000000000^3573 ≤ 10813715740211^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774846769 10000000000 10813715740211 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328561181/625000000 : ℝ), (5419072431/10000000000 : ℝ), (-1774846769/10000000000 : ℝ)] ![(43722092827643/100000000000000 : ℝ), (45464191417513/100000000000000 : ℝ), (10813715740211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328561181/625000000 : ℝ)|^4597 ≤ (43722092827643/100000000000000 : ℝ)^3573
        have hw : |(328561181/625000000 : ℝ)|=(328561181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419072431/10000000000 : ℝ)|^4597 ≤ (45464191417513/100000000000000 : ℝ)^3573
        have hw : |(5419072431/10000000000 : ℝ)|=(5419072431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1774846769/10000000000 : ℝ)|^4597 ≤ (10813715740211/100000000000000 : ℝ)^3573
        have hw : |(-1774846769/10000000000 : ℝ)|=(1774846769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_11 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4506219731/10000000000 : ℝ)*x 0 + (4131645999/10000000000 : ℝ)*x 1 + (129113939/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506219731/10000000000 : ℝ)^4597 ≤ (896472784257/2500000000000 : ℝ)^3573 := by
    have hnat : (4506219731 : ℕ)^4597*2500000000000^3573 ≤ 896472784257^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506219731 10000000000 896472784257 2500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131645999/10000000000 : ℝ)^4597 ≤ (32070544066993/100000000000000 : ℝ)^3573 := by
    have hnat : (4131645999 : ℕ)^4597*100000000000000^3573 ≤ 32070544066993^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131645999 10000000000 32070544066993 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129113939/312500000 : ℝ)^4597 ≤ (6414108911269/20000000000000 : ℝ)^3573 := by
    have hnat : (129113939 : ℕ)^4597*20000000000000^3573 ≤ 6414108911269^3573*312500000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129113939 312500000 6414108911269 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506219731/10000000000 : ℝ), (4131645999/10000000000 : ℝ), (129113939/312500000 : ℝ)] ![(896472784257/2500000000000 : ℝ), (32070544066993/100000000000000 : ℝ), (6414108911269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506219731/10000000000 : ℝ)|^4597 ≤ (896472784257/2500000000000 : ℝ)^3573
        have hw : |(4506219731/10000000000 : ℝ)|=(4506219731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131645999/10000000000 : ℝ)|^4597 ≤ (32070544066993/100000000000000 : ℝ)^3573
        have hw : |(4131645999/10000000000 : ℝ)|=(4131645999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129113939/312500000 : ℝ)|^4597 ≤ (6414108911269/20000000000000 : ℝ)^3573
        have hw : |(129113939/312500000 : ℝ)|=(129113939/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_12 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-169483323/1000000000 : ℝ)*x 0 + (343982551/625000000 : ℝ)*x 1 + (2614806229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169483323/1000000000 : ℝ)^4597 ≤ (10190593159809/100000000000000 : ℝ)^3573 := by
    have hnat : (169483323 : ℕ)^4597*100000000000000^3573 ≤ 10190593159809^3573*1000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169483323 1000000000 10190593159809 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343982551/625000000 : ℝ)^4597 ≤ (23189965644231/50000000000000 : ℝ)^3573 := by
    have hnat : (343982551 : ℕ)^4597*50000000000000^3573 ≤ 23189965644231^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343982551 625000000 23189965644231 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614806229/5000000000 : ℝ)^4597 ≤ (5428684442743/12500000000000 : ℝ)^3573 := by
    have hnat : (2614806229 : ℕ)^4597*12500000000000^3573 ≤ 5428684442743^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614806229 5000000000 5428684442743 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169483323/1000000000 : ℝ), (343982551/625000000 : ℝ), (2614806229/5000000000 : ℝ)] ![(10190593159809/100000000000000 : ℝ), (23189965644231/50000000000000 : ℝ), (5428684442743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169483323/1000000000 : ℝ)|^4597 ≤ (10190593159809/100000000000000 : ℝ)^3573
        have hw : |(-169483323/1000000000 : ℝ)|=(169483323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343982551/625000000 : ℝ)|^4597 ≤ (23189965644231/50000000000000 : ℝ)^3573
        have hw : |(343982551/625000000 : ℝ)|=(343982551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614806229/5000000000 : ℝ)|^4597 ≤ (5428684442743/12500000000000 : ℝ)^3573
        have hw : |(2614806229/5000000000 : ℝ)|=(2614806229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_13 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077701869/2000000000 : ℝ)*x 0 + (-231716273/1250000000 : ℝ)*x 1 + (5229611873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077701869/2000000000 : ℝ)^4597 ≤ (1805382308751/4000000000000 : ℝ)^3573 := by
    have hnat : (1077701869 : ℕ)^4597*4000000000000^3573 ≤ 1805382308751^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077701869 2000000000 1805382308751 4000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231716273/1250000000 : ℝ)^4597 ≤ (5717986488987/50000000000000 : ℝ)^3573 := by
    have hnat : (231716273 : ℕ)^4597*50000000000000^3573 ≤ 5717986488987^3573*1250000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231716273 1250000000 5717986488987 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229611873/10000000000 : ℝ)^4597 ≤ (21714734645739/50000000000000 : ℝ)^3573 := by
    have hnat : (5229611873 : ℕ)^4597*50000000000000^3573 ≤ 21714734645739^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229611873 10000000000 21714734645739 50000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077701869/2000000000 : ℝ), (-231716273/1250000000 : ℝ), (5229611873/10000000000 : ℝ)] ![(1805382308751/4000000000000 : ℝ), (5717986488987/50000000000000 : ℝ), (21714734645739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077701869/2000000000 : ℝ)|^4597 ≤ (1805382308751/4000000000000 : ℝ)^3573
        have hw : |(1077701869/2000000000 : ℝ)|=(1077701869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-231716273/1250000000 : ℝ)|^4597 ≤ (5717986488987/50000000000000 : ℝ)^3573
        have hw : |(-231716273/1250000000 : ℝ)|=(231716273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229611873/10000000000 : ℝ)|^4597 ≤ (21714734645739/50000000000000 : ℝ)^3573
        have hw : |(5229611873/10000000000 : ℝ)|=(5229611873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_14 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077701769/2000000000 : ℝ)*x 0 + (5229612371/10000000000 : ℝ)*x 1 + (-115858137/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077701769/2000000000 : ℝ)^4597 ≤ (5641819041309/12500000000000 : ℝ)^3573 := by
    have hnat : (1077701769 : ℕ)^4597*12500000000000^3573 ≤ 5641819041309^3573*2000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077701769 2000000000 5641819041309 12500000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229612371/10000000000 : ℝ)^4597 ≤ (10857368653097/25000000000000 : ℝ)^3573 := by
    have hnat : (5229612371 : ℕ)^4597*25000000000000^3573 ≤ 10857368653097^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229612371 10000000000 10857368653097 25000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115858137/625000000 : ℝ)^4597 ≤ (178687078773/1562500000000 : ℝ)^3573 := by
    have hnat : (115858137 : ℕ)^4597*1562500000000^3573 ≤ 178687078773^3573*625000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115858137 625000000 178687078773 1562500000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077701769/2000000000 : ℝ), (5229612371/10000000000 : ℝ), (-115858137/625000000 : ℝ)] ![(5641819041309/12500000000000 : ℝ), (10857368653097/25000000000000 : ℝ), (178687078773/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077701769/2000000000 : ℝ)|^4597 ≤ (5641819041309/12500000000000 : ℝ)^3573
        have hw : |(1077701769/2000000000 : ℝ)|=(1077701769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229612371/10000000000 : ℝ)|^4597 ≤ (10857368653097/25000000000000 : ℝ)^3573
        have hw : |(5229612371/10000000000 : ℝ)|=(5229612371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115858137/625000000 : ℝ)|^4597 ≤ (178687078773/1562500000000 : ℝ)^3573
        have hw : |(-115858137/625000000 : ℝ)|=(115858137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1550_box_15 (p : ℝ) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2003943519/5000000000 : ℝ)*x 0 + (4380804299/10000000000 : ℝ)*x 1 + (2190402277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003943519/5000000000 : ℝ)^4597 ≤ (3083993610683/10000000000000 : ℝ)^3573 := by
    have hnat : (2003943519 : ℕ)^4597*10000000000000^3573 ≤ 3083993610683^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003943519 5000000000 3083993610683 10000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380804299/10000000000 : ℝ)^4597 ≤ (34580030643893/100000000000000 : ℝ)^3573 := by
    have hnat : (4380804299 : ℕ)^4597*100000000000000^3573 ≤ 34580030643893^3573*10000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380804299 10000000000 34580030643893 100000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190402277/5000000000 : ℝ)^4597 ≤ (6916006646723/20000000000000 : ℝ)^3573 := by
    have hnat : (2190402277 : ℕ)^4597*20000000000000^3573 ≤ 6916006646723^3573*5000000000^4597 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190402277 5000000000 6916006646723 20000000000000 4597 3573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4597/1024 : ℝ)) 4597 3573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2003943519/5000000000 : ℝ), (4380804299/10000000000 : ℝ), (2190402277/5000000000 : ℝ)] ![(3083993610683/10000000000000 : ℝ), (34580030643893/100000000000000 : ℝ), (6916006646723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2003943519/5000000000 : ℝ)|^4597 ≤ (3083993610683/10000000000000 : ℝ)^3573
        have hw : |(2003943519/5000000000 : ℝ)|=(2003943519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380804299/10000000000 : ℝ)|^4597 ≤ (34580030643893/100000000000000 : ℝ)^3573
        have hw : |(4380804299/10000000000 : ℝ)|=(4380804299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190402277/5000000000 : ℝ)|^4597 ≤ (6916006646723/20000000000000 : ℝ)^3573
        have hw : |(2190402277/5000000000 : ℝ)|=(2190402277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1550_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2211/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12759/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58807/100000 : ℝ) ∧ (40359/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43121/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2211/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2211/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2211/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2211/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2211/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2211/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2211/20000 : ℝ) ^ (4595/1024 : ℝ) ≤ (5106892096097473/100000000000000000000 : ℝ) := by
    have hpowers : (2211/20000 : ℝ)^4595 ≤ (5106892096097473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2211 : ℕ)^4595*100000000000000000000^1024 ≤ 5106892096097473^1024*20000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2211 20000 5106892096097473 100000000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2211/20000 : ℝ)) (X := (5106892096097473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4595/1024 : ℝ) ≤ (2895974856976871/12500000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4595 ≤ (2895974856976871/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4595*12500000000000000000^1024 ≤ 2895974856976871^1024*20000^4595 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 2895974856976871 12500000000000000000 4595 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (2895974856976871/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005106892096097473/50000000000000000000 : ℝ) ≤ (2000045521218467/2000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (50005106892096097473/50000000000000000000 : ℝ)^1024 ≤ (2000045521218467/2000000000000000 : ℝ)^4595 := by
      have hnat : (50005106892096097473 : ℕ)^1024*2000000000000000^4595 ≤ 2000045521218467^4595*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005106892096097473 50000000000000000000 2000045521218467 2000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000045521218467/2000000000000000 : ℝ)) (X := (50005106892096097473/50000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028274690951912441/100000000000000000000 : ℝ) ≤ (50003150174431/50000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (100028274690951912441/100000000000000000000 : ℝ)^1024 ≤ (50003150174431/50000000000000 : ℝ)^4595 := by
      have hnat : (100028274690951912441 : ℕ)^1024*50000000000000^4595 ≤ 50003150174431^4595*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028274690951912441 100000000000000000000 50003150174431 50000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50003150174431/50000000000000 : ℝ)) (X := (100028274690951912441/100000000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252895974856976871/6250000000000000000 : ℝ) ≤ (2000206492736013/2000000000000000 : ℝ) ^ (4595/1024 : ℝ) := by
    have hpowers : (6252895974856976871/6250000000000000000 : ℝ)^1024 ≤ (2000206492736013/2000000000000000 : ℝ)^4595 := by
      have hnat : (6252895974856976871 : ℕ)^1024*2000000000000000^4595 ≤ 2000206492736013^4595*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252895974856976871 6250000000000000000 2000206492736013 2000000000000000 1024 4595 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000206492736013/2000000000000000 : ℝ)) (X := (6252895974856976871/6250000000000000000 : ℝ)) (by norm_num) 4595 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5106892096097473/100000000000000000000 : ℝ) ≤ ((442921105943566889/443000000000000000 : ℝ)+2*(80485758773/88600000000000 : ℝ)*(2211/20000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (442921105943566889/443000000000000000 : ℝ)+2*(80485758773/88600000000000 : ℝ)*(2211/20000 : ℝ)=(2000045521218467/2000000000000000 : ℝ) by norm_num, show 1+2*(5106892096097473/100000000000000000000 : ℝ)=(50005106892096097473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2895974856976871/12500000000000000000 : ℝ)+(5106892096097473/100000000000000000000 : ℝ) ≤ ((442921105943566889/443000000000000000 : ℝ)+(80485758773/88600000000000 : ℝ)*((3097/20000 : ℝ)+(2211/20000 : ℝ)))^(4595/1024 : ℝ) := by
    rw [show (442921105943566889/443000000000000000 : ℝ)+(80485758773/88600000000000 : ℝ)*((3097/20000 : ℝ)+(2211/20000 : ℝ))=(50003150174431/50000000000000 : ℝ) by norm_num, show 1+(2895974856976871/12500000000000000000 : ℝ)+(5106892096097473/100000000000000000000 : ℝ)=(100028274690951912441/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2895974856976871/12500000000000000000 : ℝ) ≤ ((442921105943566889/443000000000000000 : ℝ)+2*(80485758773/88600000000000 : ℝ)*(3097/20000 : ℝ))^(4595/1024 : ℝ) := by
    rw [show (442921105943566889/443000000000000000 : ℝ)+2*(80485758773/88600000000000 : ℝ)*(3097/20000 : ℝ)=(2000206492736013/2000000000000000 : ℝ) by norm_num, show 1+2*(2895974856976871/12500000000000000000 : ℝ)=(6252895974856976871/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (442921105943566889/443000000000000000 : ℝ)*(X 1 0+X 2 0)+(80485758773/88600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (2211/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (442921105943566889/443000000000000000 : ℝ)) (alpha := (80485758773/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (442921105943566889/443000000000000000 : ℝ)*(X 0 1+X 2 1)+(80485758773/88600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (2211/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (442921105943566889/443000000000000000 : ℝ)) (alpha := (80485758773/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (442921105943566889/443000000000000000 : ℝ)*(X 0 2+X 1 2)+(80485758773/88600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4595/1024 : ℝ)) (lo := (2211/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (442921105943566889/443000000000000000 : ℝ)) (alpha := (80485758773/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401558439/2500000000 : ℝ)*X 0 0+(5398736181/10000000000 : ℝ)*X 0 1+(5398737317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271100031/10000000000 : ℝ)*X 1 0+(-1783543617/10000000000 : ℝ)*X 1 1+(269936853/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((527109991/1000000000 : ℝ)*X 2 0+(1079747481/2000000000 : ℝ)*X 2 1+(-1783543307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((890769791/2000000000 : ℝ)*X 0 0+(1039605479/2500000000 : ℝ)*X 0 1+(4158420459/10000000000 : ℝ)*X 0 2+(890769791/2000000000 : ℝ)*X 1 0+(1039605479/2500000000 : ℝ)*X 1 1+(4158420459/10000000000 : ℝ)*X 1 2+(890769791/2000000000 : ℝ)*X 2 0+(1039605479/2500000000 : ℝ)*X 2 1+(4158420459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025784333/10000000000 : ℝ)*X 0 0+(5244659139/10000000000 : ℝ)*X 0 1+(1048931851/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5378061767/10000000000 : ℝ)*X 1 0+(-230955431/1250000000 : ℝ)*X 1 1+(8194781/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378063681/10000000000 : ℝ)*X 2 0+(5244658703/10000000000 : ℝ)*X 2 1+(-1847642381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2024174337/5000000000 : ℝ)*X 0 0+(272565117/625000000 : ℝ)*X 0 1+(2180520741/5000000000 : ℝ)*X 0 2+(2024174337/5000000000 : ℝ)*X 1 0+(272565117/625000000 : ℝ)*X 1 1+(2180520741/5000000000 : ℝ)*X 1 2+(2024174337/5000000000 : ℝ)*X 2 0+(272565117/625000000 : ℝ)*X 2 1+(2180520741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1936940017/10000000000 : ℝ)*X 0 0+(5136313803/10000000000 : ℝ)*X 0 1+(1354768053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628489459/5000000000 : ℝ)*X 1 0+(-1774846771/10000000000 : ℝ)*X 1 1+(677384051/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((328561181/625000000 : ℝ)*X 2 0+(5419072431/10000000000 : ℝ)*X 2 1+(-1774846769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4506219731/10000000000 : ℝ)*X 0 0+(4131645999/10000000000 : ℝ)*X 0 1+(129113939/312500000 : ℝ)*X 0 2+(4506219731/10000000000 : ℝ)*X 1 0+(4131645999/10000000000 : ℝ)*X 1 1+(129113939/312500000 : ℝ)*X 1 2+(4506219731/10000000000 : ℝ)*X 2 0+(4131645999/10000000000 : ℝ)*X 2 1+(129113939/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-169483323/1000000000 : ℝ)*X 0 0+(343982551/625000000 : ℝ)*X 0 1+(2614806229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1077701869/2000000000 : ℝ)*X 1 0+(-231716273/1250000000 : ℝ)*X 1 1+(5229611873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1077701769/2000000000 : ℝ)*X 2 0+(5229612371/10000000000 : ℝ)*X 2 1+(-115858137/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2003943519/5000000000 : ℝ)*X 0 0+(4380804299/10000000000 : ℝ)*X 0 1+(2190402277/5000000000 : ℝ)*X 0 2+(2003943519/5000000000 : ℝ)*X 1 0+(4380804299/10000000000 : ℝ)*X 1 1+(2190402277/5000000000 : ℝ)*X 1 2+(2003943519/5000000000 : ℝ)*X 2 0+(4380804299/10000000000 : ℝ)*X 2 1+(2190402277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1550_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12759/20000 : ℝ) ≤ (-3532503336858685304300349196413/5537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34434607/20000000000000 : ℝ)*(upper0) + (11536039/2000000000000 : ℝ)*(lower2) + (138953843/100000000000000 : ℝ)*(upper5) + (1139482478443739/50000000000000 : ℝ)*(major0) + (1139482478443739/50000000000000 : ℝ)*(major1) + (1139482478443739/50000000000000 : ℝ)*(major2) + (474099207/50000000000000 : ℝ)*(sp2) + (731486689/10000000000000 : ℝ)*(sp3) + (802448489318977/25000000000000 : ℝ)*(sp4) + (1604888110981517/50000000000000 : ℝ)*(sp5) + (12538287153827/390625000000 : ℝ)*(sp6) + (21396629183883/1562500000000 : ℝ)*(sp7) + (8502302219/100000000000000 : ℝ)*(sp8) + (26237615093/100000000000000 : ℝ)*(sp13) + (684695791317701/50000000000000 : ℝ)*(f.failure) + (3209802459578127/100000000000000 : ℝ)*(f.sum) + (1075986004609/1107500000000000000000000000 : ℝ)*base66 + (350453716059042971/22150000000000000000000000000000 : ℝ)*base67 + (50889662827692971/22150000000000000000000000000000 : ℝ)*base69 + (49368633921157029/22150000000000000000000000000000 : ℝ)*base72 + (4824416930153/2215000000000000000000000000 : ℝ)*base74 + (18737015628542971/22150000000000000000000000000000 : ℝ)*base75 + (83116774583492971/22150000000000000000000000000000 : ℝ)*base77 + (41727965474492971/22150000000000000000000000000000 : ℝ)*base79 + (6315334679413/2215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2055443/1000000000000000000000 : ℝ)*base89 + (2055443/1000000000000000000000 : ℝ)*base91 + (2055443/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58807/100000 : ℝ) ≤ (651318444706606261638882861/1107500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2157683/3125000000000 : ℝ)*(upper1) + (34888427/25000000000000 : ℝ)*(upper3) + (2671799/2000000000000 : ℝ)*(upper4) + (1178912351510869/50000000000000 : ℝ)*(major0) + (1178912351510869/50000000000000 : ℝ)*(major1) + (1178912351510869/50000000000000 : ℝ)*(major2) + (1639628942170187/50000000000000 : ℝ)*(sp0) + (819816709492229/25000000000000 : ℝ)*(sp1) + (3279250639152169/100000000000000 : ℝ)*(sp2) + (141677462897849/10000000000000 : ℝ)*(sp3) + (2230880159/100000000000000 : ℝ)*(sp5) + (9214848453/50000000000000 : ℝ)*(sp6) + (305533359/12500000000000 : ℝ)*(sp7) + (11184508701/100000000000000 : ℝ)*(sp12) + (708388536622681/50000000000000 : ℝ)*(f.failure) + (131170762753963/4000000000000 : ℝ)*(f.sum) + (11901788254377/2215000000000000000000000000 : ℝ)*base65 + (9492917857398459/22150000000000000000000000000000 : ℝ)*base68 + (300103174853798459/22150000000000000000000000000000 : ℝ)*base70 + (148481323082651541/22150000000000000000000000000000 : ℝ)*base71 + (3393115792437/2215000000000000000000000000 : ℝ)*base73 + (291416830072601541/22150000000000000000000000000000 : ℝ)*base75 + (17808881075398459/22150000000000000000000000000000 : ℝ)*base78 + (10163819378651541/22150000000000000000000000000000 : ℝ)*base79 + (2742745228781/1107500000000000000000000000 : ℝ)*base81 + (4016417/1000000000000000000000 : ℝ)*base90 + (4016417/1000000000000000000000 : ℝ)*base92 + (4016417/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40359/50000 : ℝ) ≤ (893978210074699137749938771887/1107500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11369731/25000000000000 : ℝ)*(upper0) + (608157/3125000000000 : ℝ)*(upper1) + (692907/100000000000000 : ℝ)*(upper2) + (27932849/100000000000000 : ℝ)*(upper3) + (4674083/50000000000000 : ℝ)*(upper4) + (254695909201161/10000000000000 : ℝ)*(major0) + (254695909201161/10000000000000 : ℝ)*(major1) + (254695909201161/10000000000000 : ℝ)*(major2) + (2992094043/10000000000000 : ℝ)*(sp1) + (207801817/500000000000 : ℝ)*(sp2) + (3536586654897143/100000000000000 : ℝ)*(sp8) + (1768278366978357/50000000000000 : ℝ)*(sp9) + (221034068408359/6250000000000 : ℝ)*(sp10) + (765212367872669/50000000000000 : ℝ)*(sp11) + (765212367872669/50000000000000 : ℝ)*(f.failure) + (3536586654897143/100000000000000 : ℝ)*(f.sum) + (34233903097/1730468750000000000000000 : ℝ)*base65 + (32377641347906871/4430000000000000000000000000000 : ℝ)*base68 + (25200363774976871/4430000000000000000000000000000 : ℝ)*base70 + (5588569132576871/4430000000000000000000000000000 : ℝ)*base72 + (3545780327359/443000000000000000000000000 : ℝ)*base73 + (41359199861256871/4430000000000000000000000000000 : ℝ)*base76 + (11553529207363129/4430000000000000000000000000000 : ℝ)*base77 + (35684298936956871/4430000000000000000000000000000 : ℝ)*base80 + (509329666869/443000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4678533/1000000000000000000000 : ℝ)*base90 + (4678533/1000000000000000000000 : ℝ)*base92 + (4678533/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-43121/50000 : ℝ) ≤ (-9551079856840157417235222844893/11075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13836143/6250000000000 : ℝ)*(upper3) + (46271197/50000000000000 : ℝ)*(lower4) + (25723781/12500000000000 : ℝ)*(upper5) + (1293478077151107/50000000000000 : ℝ)*(major0) + (1293478077151107/50000000000000 : ℝ)*(major1) + (1293478077151107/50000000000000 : ℝ)*(major2) + (1476783293/25000000000000 : ℝ)*(sp4) + (147424024229/50000000000000 : ℝ)*(sp5) + (1631864321/781250000000 : ℝ)*(sp6) + (10252780293/20000000000000 : ℝ)*(sp7) + (3648194772224253/100000000000000 : ℝ)*(sp12) + (455988228913621/12500000000000 : ℝ)*(sp13) + (3647991800724337/100000000000000 : ℝ)*(sp14) + (777203515790659/50000000000000 : ℝ)*(sp15) + (1554458295482783/100000000000000 : ℝ)*(f.failure) + (145928027174297/4000000000000 : ℝ)*(f.sum) + (2453861180309/2215000000000000000000000000 : ℝ)*base66 + (94069913310248877/22150000000000000000000000000000 : ℝ)*base68 + (268357323823948877/22150000000000000000000000000000 : ℝ)*base70 + (112240373917548877/22150000000000000000000000000000 : ℝ)*base72 + (708204702479/2215000000000000000000000000 : ℝ)*base74 + (209102818881448877/22150000000000000000000000000000 : ℝ)*base76 + (126538784718598877/22150000000000000000000000000000 : ℝ)*base78 + (84831780360498877/22150000000000000000000000000000 : ℝ)*base80 + (13222008463339/2215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19966569/2000000000000000000000 : ℝ)*base89 + (19966569/2000000000000000000000 : ℝ)*base91 + (19966569/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1550_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2211/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12759/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58807/100000 : ℝ) else (40359/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43121/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1550_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1550_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12759/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58807/100000 : ℝ) else (40359/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43121/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1550_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1550_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4595/1024 : ℝ) ≤ p) (hpb : p ≤ (4597/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33284343/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12759/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58807/100000 : ℝ) else (40359/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43121/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1550_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
