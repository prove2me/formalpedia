-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:50.330011+00:00
-- url     : https://prove2.me/submissions/e385c9b1-653d-48da-927a-1b43fe4d7684

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
theorem support_rectangle_w1571_s3_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892001581/5000000000 : ℝ)*x 0 + (678414537/1250000000 : ℝ)*x 1 + (2609303211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892001581/5000000000 : ℝ)^4639 ≤ (10948202361347/100000000000000 : ℝ)^3615 := by
    have hnat : (892001581 : ℕ)^4639*100000000000000^3615 ≤ 10948202361347^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892001581 5000000000 10948202361347 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678414537/1250000000 : ℝ)^4639 ≤ (9129197527569/20000000000000 : ℝ)^3615 := by
    have hnat : (678414537 : ℕ)^4639*20000000000000^3615 ≤ 9129197527569^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678414537 1250000000 9129197527569 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609303211/5000000000 : ℝ)^4639 ≤ (43405809978409/100000000000000 : ℝ)^3615 := by
    have hnat : (2609303211 : ℕ)^4639*100000000000000^3615 ≤ 43405809978409^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609303211 5000000000 43405809978409 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892001581/5000000000 : ℝ), (678414537/1250000000 : ℝ), (2609303211/5000000000 : ℝ)] ![(10948202361347/100000000000000 : ℝ), (9129197527569/20000000000000 : ℝ), (43405809978409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892001581/5000000000 : ℝ)|^4639 ≤ (10948202361347/100000000000000 : ℝ)^3615
        have hw : |(-892001581/5000000000 : ℝ)|=(892001581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678414537/1250000000 : ℝ)|^4639 ≤ (9129197527569/20000000000000 : ℝ)^3615
        have hw : |(678414537/1250000000 : ℝ)|=(678414537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609303211/5000000000 : ℝ)|^4639 ≤ (43405809978409/100000000000000 : ℝ)^3615
        have hw : |(2609303211/5000000000 : ℝ)|=(2609303211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348567159/10000000000 : ℝ)*x 0 + (-945405509/5000000000 : ℝ)*x 1 + (5218606463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348567159/10000000000 : ℝ)^4639 ≤ (2239890890889/5000000000000 : ℝ)^3615 := by
    have hnat : (5348567159 : ℕ)^4639*5000000000000^3615 ≤ 2239890890889^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348567159 10000000000 2239890890889 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945405509/5000000000 : ℝ)^4639 ≤ (2359274350737/20000000000000 : ℝ)^3615 := by
    have hnat : (945405509 : ℕ)^4639*20000000000000^3615 ≤ 2359274350737^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945405509 5000000000 2359274350737 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218606463/10000000000 : ℝ)^4639 ≤ (1736232416641/4000000000000 : ℝ)^3615 := by
    have hnat : (5218606463 : ℕ)^4639*4000000000000^3615 ≤ 1736232416641^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218606463 10000000000 1736232416641 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348567159/10000000000 : ℝ), (-945405509/5000000000 : ℝ), (5218606463/10000000000 : ℝ)] ![(2239890890889/5000000000000 : ℝ), (2359274350737/20000000000000 : ℝ), (1736232416641/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348567159/10000000000 : ℝ)|^4639 ≤ (2239890890889/5000000000000 : ℝ)^3615
        have hw : |(5348567159/10000000000 : ℝ)|=(5348567159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945405509/5000000000 : ℝ)|^4639 ≤ (2359274350737/20000000000000 : ℝ)^3615
        have hw : |(-945405509/5000000000 : ℝ)|=(945405509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218606463/10000000000 : ℝ)|^4639 ≤ (1736232416641/4000000000000 : ℝ)^3615
        have hw : |(5218606463/10000000000 : ℝ)|=(5218606463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674283643/5000000000 : ℝ)*x 0 + (5218606239/10000000000 : ℝ)*x 1 + (-945405573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674283643/5000000000 : ℝ)^4639 ≤ (44797819182801/100000000000000 : ℝ)^3615 := by
    have hnat : (2674283643 : ℕ)^4639*100000000000000^3615 ≤ 44797819182801^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674283643 5000000000 44797819182801 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218606239/10000000000 : ℝ)^4639 ≤ (43405808025147/100000000000000 : ℝ)^3615 := by
    have hnat : (5218606239 : ℕ)^4639*100000000000000^3615 ≤ 43405808025147^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218606239 10000000000 43405808025147 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945405573/5000000000 : ℝ)^4639 ≤ (5898186389227/50000000000000 : ℝ)^3615 := by
    have hnat : (945405573 : ℕ)^4639*50000000000000^3615 ≤ 5898186389227^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945405573 5000000000 5898186389227 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674283643/5000000000 : ℝ), (5218606239/10000000000 : ℝ), (-945405573/5000000000 : ℝ)] ![(44797819182801/100000000000000 : ℝ), (43405808025147/100000000000000 : ℝ), (5898186389227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674283643/5000000000 : ℝ)|^4639 ≤ (44797819182801/100000000000000 : ℝ)^3615
        have hw : |(2674283643/5000000000 : ℝ)|=(2674283643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218606239/10000000000 : ℝ)|^4639 ≤ (43405808025147/100000000000000 : ℝ)^3615
        have hw : |(5218606239/10000000000 : ℝ)|=(5218606239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945405573/5000000000 : ℝ)|^4639 ≤ (5898186389227/50000000000000 : ℝ)^3615
        have hw : |(-945405573/5000000000 : ℝ)|=(945405573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060727267/2500000000 : ℝ)*x 0 + (500275067/1250000000 : ℝ)*x 1 + (4495208231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060727267/2500000000 : ℝ)^4639 ≤ (33280833586583/100000000000000 : ℝ)^3615 := by
    have hnat : (1060727267 : ℕ)^4639*100000000000000^3615 ≤ 33280833586583^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060727267 2500000000 33280833586583 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500275067/1250000000 : ℝ)^4639 ≤ (30877658211397/100000000000000 : ℝ)^3615 := by
    have hnat : (500275067 : ℕ)^4639*100000000000000^3615 ≤ 30877658211397^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500275067 1250000000 30877658211397 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495208231/10000000000 : ℝ)^4639 ≤ (35841508189499/100000000000000 : ℝ)^3615 := by
    have hnat : (4495208231 : ℕ)^4639*100000000000000^3615 ≤ 35841508189499^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495208231 10000000000 35841508189499 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060727267/2500000000 : ℝ), (500275067/1250000000 : ℝ), (4495208231/10000000000 : ℝ)] ![(33280833586583/100000000000000 : ℝ), (30877658211397/100000000000000 : ℝ), (35841508189499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060727267/2500000000 : ℝ)|^4639 ≤ (33280833586583/100000000000000 : ℝ)^3615
        have hw : |(1060727267/2500000000 : ℝ)|=(1060727267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500275067/1250000000 : ℝ)|^4639 ≤ (30877658211397/100000000000000 : ℝ)^3615
        have hw : |(500275067/1250000000 : ℝ)|=(500275067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495208231/10000000000 : ℝ)|^4639 ≤ (35841508189499/100000000000000 : ℝ)^3615
        have hw : |(4495208231/10000000000 : ℝ)|=(4495208231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71361243/400000000 : ℝ)*x 0 + (5219710249/10000000000 : ℝ)*x 1 + (5426204231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71361243/400000000 : ℝ)^4639 ≤ (10948422183139/100000000000000 : ℝ)^3615 := by
    have hnat : (71361243 : ℕ)^4639*100000000000000^3615 ≤ 10948422183139^3615*400000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71361243 400000000 10948422183139 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219710249/10000000000 : ℝ)^4639 ≤ (10854398024413/25000000000000 : ℝ)^3615 := by
    have hnat : (5219710249 : ℕ)^4639*25000000000000^3615 ≤ 10854398024413^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219710249 10000000000 10854398024413 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426204231/10000000000 : ℝ)^4639 ≤ (2281699285357/5000000000000 : ℝ)^3615 := by
    have hnat : (5426204231 : ℕ)^4639*5000000000000^3615 ≤ 2281699285357^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426204231 10000000000 2281699285357 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71361243/400000000 : ℝ), (5219710249/10000000000 : ℝ), (5426204231/10000000000 : ℝ)] ![(10948422183139/100000000000000 : ℝ), (10854398024413/25000000000000 : ℝ), (2281699285357/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71361243/400000000 : ℝ)|^4639 ≤ (10948422183139/100000000000000 : ℝ)^3615
        have hw : |(-71361243/400000000 : ℝ)|=(71361243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219710249/10000000000 : ℝ)|^4639 ≤ (10854398024413/25000000000000 : ℝ)^3615
        have hw : |(5219710249/10000000000 : ℝ)|=(5219710249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426204231/10000000000 : ℝ)|^4639 ≤ (2281699285357/5000000000000 : ℝ)^3615
        have hw : |(5426204231/10000000000 : ℝ)|=(5426204231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293341999/10000000000 : ℝ)*x 0 + (-84160661/500000000 : ℝ)*x 1 + (271310209/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293341999/10000000000 : ℝ)^4639 ≤ (5525639661279/12500000000000 : ℝ)^3615 := by
    have hnat : (5293341999 : ℕ)^4639*12500000000000^3615 ≤ 5525639661279^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293341999 10000000000 5525639661279 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84160661/500000000 : ℝ)^4639 ≤ (10160897537009/100000000000000 : ℝ)^3615 := by
    have hnat : (84160661 : ℕ)^4639*100000000000000^3615 ≤ 10160897537009^3615*500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84160661 500000000 10160897537009 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271310209/500000000 : ℝ)^4639 ≤ (2281699257837/5000000000000 : ℝ)^3615 := by
    have hnat : (271310209 : ℕ)^4639*5000000000000^3615 ≤ 2281699257837^3615*500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271310209 500000000 2281699257837 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293341999/10000000000 : ℝ), (-84160661/500000000 : ℝ), (271310209/500000000 : ℝ)] ![(5525639661279/12500000000000 : ℝ), (10160897537009/100000000000000 : ℝ), (2281699257837/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293341999/10000000000 : ℝ)|^4639 ≤ (5525639661279/12500000000000 : ℝ)^3615
        have hw : |(5293341999/10000000000 : ℝ)|=(5293341999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84160661/500000000 : ℝ)|^4639 ≤ (10160897537009/100000000000000 : ℝ)^3615
        have hw : |(-84160661/500000000 : ℝ)|=(84160661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271310209/500000000 : ℝ)|^4639 ≤ (2281699257837/5000000000000 : ℝ)^3615
        have hw : |(271310209/500000000 : ℝ)|=(271310209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323335507/2500000000 : ℝ)*x 0 + (542620423/1000000000 : ℝ)*x 1 + (-168321311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323335507/2500000000 : ℝ)^4639 ≤ (22102558800507/50000000000000 : ℝ)^3615 := by
    have hnat : (1323335507 : ℕ)^4639*50000000000000^3615 ≤ 22102558800507^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323335507 2500000000 22102558800507 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542620423/1000000000 : ℝ)^4639 ≤ (11408496424087/25000000000000 : ℝ)^3615 := by
    have hnat : (542620423 : ℕ)^4639*25000000000000^3615 ≤ 11408496424087^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542620423 1000000000 11408496424087 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168321311/1000000000 : ℝ)^4639 ≤ (1270112085611/12500000000000 : ℝ)^3615 := by
    have hnat : (168321311 : ℕ)^4639*12500000000000^3615 ≤ 1270112085611^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168321311 1000000000 1270112085611 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323335507/2500000000 : ℝ), (542620423/1000000000 : ℝ), (-168321311/1000000000 : ℝ)] ![(22102558800507/50000000000000 : ℝ), (11408496424087/25000000000000 : ℝ), (1270112085611/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323335507/2500000000 : ℝ)|^4639 ≤ (22102558800507/50000000000000 : ℝ)^3615
        have hw : |(1323335507/2500000000 : ℝ)|=(1323335507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542620423/1000000000 : ℝ)|^4639 ≤ (11408496424087/25000000000000 : ℝ)^3615
        have hw : |(542620423/1000000000 : ℝ)|=(542620423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168321311/1000000000 : ℝ)|^4639 ≤ (1270112085611/12500000000000 : ℝ)^3615
        have hw : |(-168321311/1000000000 : ℝ)|=(168321311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s3_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242975781/10000000000 : ℝ)*x 0 + (140393771/312500000 : ℝ)*x 1 + (1001206759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242975781/10000000000 : ℝ)^4639 ≤ (832037627627/2500000000000 : ℝ)^3615 := by
    have hnat : (4242975781 : ℕ)^4639*2500000000000^3615 ≤ 832037627627^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242975781 10000000000 832037627627 2500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140393771/312500000 : ℝ)^4639 ≤ (17907415164731/50000000000000 : ℝ)^3615 := by
    have hnat : (140393771 : ℕ)^4639*50000000000000^3615 ≤ 17907415164731^3615*312500000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140393771 312500000 17907415164731 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001206759/2500000000 : ℝ)^4639 ≤ (482869758717/1562500000000 : ℝ)^3615 := by
    have hnat : (1001206759 : ℕ)^4639*1562500000000^3615 ≤ 482869758717^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001206759 2500000000 482869758717 1562500000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242975781/10000000000 : ℝ), (140393771/312500000 : ℝ), (1001206759/2500000000 : ℝ)] ![(832037627627/2500000000000 : ℝ), (17907415164731/50000000000000 : ℝ), (482869758717/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242975781/10000000000 : ℝ)|^4639 ≤ (832037627627/2500000000000 : ℝ)^3615
        have hw : |(4242975781/10000000000 : ℝ)|=(4242975781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140393771/312500000 : ℝ)|^4639 ≤ (17907415164731/50000000000000 : ℝ)^3615
        have hw : |(140393771/312500000 : ℝ)|=(140393771/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001206759/2500000000 : ℝ)|^4639 ≤ (482869758717/1562500000000 : ℝ)^3615
        have hw : |(1001206759/2500000000 : ℝ)|=(1001206759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11093/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15519/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (433/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15809/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (433/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (433/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15809/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (433/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (433/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15809/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (433/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (433/4000 : ℝ) ^ (4637/1024 : ℝ) ≤ (2121046909072643/50000000000000000000 : ℝ) := by
    have hpowers : (433/4000 : ℝ)^4637 ≤ (2121046909072643/50000000000000000000 : ℝ)^1024 := by
      have hnat : (433 : ℕ)^4637*50000000000000000000^1024 ≤ 2121046909072643^1024*4000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        433 4000 2121046909072643 50000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (433/4000 : ℝ)) (X := (2121046909072643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15809/100000 : ℝ) ^ (4637/1024 : ℝ) ≤ (1178562244170451/5000000000000000000 : ℝ) := by
    have hpowers : (15809/100000 : ℝ)^4637 ≤ (1178562244170451/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15809 : ℕ)^4637*5000000000000000000^1024 ≤ 1178562244170451^1024*100000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15809 100000 1178562244170451 5000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15809/100000 : ℝ)) (X := (1178562244170451/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002121046909072643/25000000000000000000 : ℝ) ≤ (10000187352188823/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (25002121046909072643/25000000000000000000 : ℝ)^1024 ≤ (10000187352188823/10000000000000000 : ℝ)^4637 := by
      have hnat : (25002121046909072643 : ℕ)^1024*10000000000000000^4637 ≤ 10000187352188823^4637*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002121046909072643 25000000000000000000 10000187352188823 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000187352188823/10000000000000000 : ℝ)) (X := (25002121046909072643/25000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013906669350777153/50000000000000000000 : ℝ) ≤ (2000122828437611/2000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50013906669350777153/50000000000000000000 : ℝ)^1024 ≤ (2000122828437611/2000000000000000 : ℝ)^4637 := by
      have hnat : (50013906669350777153 : ℕ)^1024*2000000000000000^4637 ≤ 2000122828437611^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013906669350777153 50000000000000000000 2000122828437611 2000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000122828437611/2000000000000000 : ℝ)) (X := (50013906669350777153/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501178562244170451/2500000000000000000 : ℝ) ≤ (10001040932187287/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (2501178562244170451/2500000000000000000 : ℝ)^1024 ≤ (10001040932187287/10000000000000000 : ℝ)^4637 := by
      have hnat : (2501178562244170451 : ℕ)^1024*10000000000000000^4637 ≤ 10001040932187287^4637*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501178562244170451 2500000000000000000 10001040932187287 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001040932187287/10000000000000000 : ℝ)) (X := (2501178562244170451/2500000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2121046909072643/50000000000000000000 : ℝ) ≤ ((6228961719978215129/6230000000000000000 : ℝ)+2*(3334296869/3893750000000 : ℝ)*(433/4000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (6228961719978215129/6230000000000000000 : ℝ)+2*(3334296869/3893750000000 : ℝ)*(433/4000 : ℝ)=(10000187352188823/10000000000000000 : ℝ) by norm_num, show 1+2*(2121046909072643/50000000000000000000 : ℝ)=(25002121046909072643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1178562244170451/5000000000000000000 : ℝ)+(2121046909072643/50000000000000000000 : ℝ) ≤ ((6228961719978215129/6230000000000000000 : ℝ)+(3334296869/3893750000000 : ℝ)*((15809/100000 : ℝ)+(433/4000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (6228961719978215129/6230000000000000000 : ℝ)+(3334296869/3893750000000 : ℝ)*((15809/100000 : ℝ)+(433/4000 : ℝ))=(2000122828437611/2000000000000000 : ℝ) by norm_num, show 1+(1178562244170451/5000000000000000000 : ℝ)+(2121046909072643/50000000000000000000 : ℝ)=(50013906669350777153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1178562244170451/5000000000000000000 : ℝ) ≤ ((6228961719978215129/6230000000000000000 : ℝ)+2*(3334296869/3893750000000 : ℝ)*(15809/100000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (6228961719978215129/6230000000000000000 : ℝ)+2*(3334296869/3893750000000 : ℝ)*(15809/100000 : ℝ)=(10001040932187287/10000000000000000 : ℝ) by norm_num, show 1+2*(1178562244170451/5000000000000000000 : ℝ)=(2501178562244170451/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6228961719978215129/6230000000000000000 : ℝ)*(X 1 0+X 2 0)+(3334296869/3893750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (6228961719978215129/6230000000000000000 : ℝ)) (alpha := (3334296869/3893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6228961719978215129/6230000000000000000 : ℝ)*(X 0 1+X 2 1)+(3334296869/3893750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (6228961719978215129/6230000000000000000 : ℝ)) (alpha := (3334296869/3893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6228961719978215129/6230000000000000000 : ℝ)*(X 0 2+X 1 2)+(3334296869/3893750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (15809/100000 : ℝ)) (c := (6228961719978215129/6230000000000000000 : ℝ)) (alpha := (3334296869/3893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892001581/5000000000 : ℝ)*X 0 0+(678414537/1250000000 : ℝ)*X 0 1+(2609303211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348567159/10000000000 : ℝ)*X 1 0+(-945405509/5000000000 : ℝ)*X 1 1+(5218606463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674283643/5000000000 : ℝ)*X 2 0+(5218606239/10000000000 : ℝ)*X 2 1+(-945405573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1060727267/2500000000 : ℝ)*X 0 0+(500275067/1250000000 : ℝ)*X 0 1+(4495208231/10000000000 : ℝ)*X 0 2+(1060727267/2500000000 : ℝ)*X 1 0+(500275067/1250000000 : ℝ)*X 1 1+(4495208231/10000000000 : ℝ)*X 1 2+(1060727267/2500000000 : ℝ)*X 2 0+(500275067/1250000000 : ℝ)*X 2 1+(4495208231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-71361243/400000000 : ℝ)*X 0 0+(5219710249/10000000000 : ℝ)*X 0 1+(5426204231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293341999/10000000000 : ℝ)*X 1 0+(-84160661/500000000 : ℝ)*X 1 1+(271310209/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323335507/2500000000 : ℝ)*X 2 0+(542620423/1000000000 : ℝ)*X 2 1+(-168321311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242975781/10000000000 : ℝ)*X 0 0+(140393771/312500000 : ℝ)*X 0 1+(1001206759/2500000000 : ℝ)*X 0 2+(4242975781/10000000000 : ℝ)*X 1 0+(140393771/312500000 : ℝ)*X 1 1+(1001206759/2500000000 : ℝ)*X 1 2+(4242975781/10000000000 : ℝ)*X 2 0+(140393771/312500000 : ℝ)*X 2 1+(1001206759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6202345691127475875927/1557500000000000000000000000 : ℝ) := by norm_num
    linear_combination (72352781/20000000000000 : ℝ)*(base19) + (266598667/50000000000000 : ℝ)*(base23) + (19894283/20000000000000 : ℝ)*(upper2) + (70254049/100000000000000 : ℝ)*(upper3) + (17157321/25000000000000 : ℝ)*(upper4) + (1704930939220753/50000000000000 : ℝ)*(major0) + (1704930939220753/50000000000000 : ℝ)*(major1) + (1704930939220753/50000000000000 : ℝ)*(major2) + (2395674068832853/50000000000000 : ℝ)*(sp0) + (29945960438667/625000000000 : ℝ)*(sp1) + (4791353498753291/100000000000000 : ℝ)*(sp2) + (507091829457787/25000000000000 : ℝ)*(sp3) + (5894284919/100000000000000 : ℝ)*(sp4) + (1137179877/50000000000000 : ℝ)*(sp7) + (1014184796095451/50000000000000 : ℝ)*(f.failure) + (7666166451121/160000000000 : ℝ)*(f.sum) + (21977974213709/3115000000000000000000000000 : ℝ)*base65 + (9413092962072137/311500000000000000000000000000000 : ℝ)*base67 + (199140745432927863/311500000000000000000000000000000 : ℝ)*base70 + (487387851380427863/311500000000000000000000000000000 : ℝ)*base72 + (73879429781/48671875000000000000000000 : ℝ)*base73 + (3604051488768572137/311500000000000000000000000000000 : ℝ)*base75 + (746927862740572137/311500000000000000000000000000000 : ℝ)*base77 + (1027820461170927863/311500000000000000000000000000000 : ℝ)*base80 + (4762165645067/1557500000000000000000000000 : ℝ)*base81 + (10707441/5000000000000000000000 : ℝ)*base90 + (10707441/5000000000000000000000 : ℝ)*base92 + (10707441/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (573287443371026052123621963/77875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152484197/12500000000000 : ℝ)*(base19) + (641580237/50000000000000 : ℝ)*(base23) + (128429317/100000000000000 : ℝ)*(upper3) + (9387561/100000000000000 : ℝ)*(lower4) + (88190349/50000000000000 : ℝ)*(upper5) + (1723222206129049/50000000000000 : ℝ)*(major0) + (1723222206129049/50000000000000 : ℝ)*(major1) + (1723222206129049/50000000000000 : ℝ)*(major2) + (19500112601/100000000000000 : ℝ)*(sp1) + (21323223063/100000000000000 : ℝ)*(sp2) + (484275772450387/10000000000000 : ℝ)*(sp4) + (4842737004517693/100000000000000 : ℝ)*(sp5) + (4842735118120333/100000000000000 : ℝ)*(sp6) + (2050130854624437/100000000000000 : ℝ)*(sp7) + (2050130854624437/100000000000000 : ℝ)*(f.failure) + (484275772450387/10000000000000 : ℝ)*(f.sum) + (16304640576187/3115000000000000000000000000 : ℝ)*base65 + (1713849509693217679/311500000000000000000000000000000 : ℝ)*base68 + (1900863957285217679/311500000000000000000000000000000 : ℝ)*base70 + (1165682359886717679/311500000000000000000000000000000 : ℝ)*base72 + (1468173954899/1557500000000000000000000000 : ℝ)*base74 + (691743367935282321/311500000000000000000000000000000 : ℝ)*base75 + (3740732457660717679/311500000000000000000000000000000 : ℝ)*base78 + (2976961767488717679/311500000000000000000000000000000 : ℝ)*base80 + (567638009171/389375000000000000000000000 : ℝ)*base82 + (59034433/10000000000000000000000 : ℝ)*base89 + (59034433/10000000000000000000000 : ℝ)*base91 + (59034433/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1571_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1571_s4_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784224813/10000000000 : ℝ)*x 0 + (5425822593/10000000000 : ℝ)*x 1 + (5219953159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784224813/10000000000 : ℝ)^4639 ≤ (43799791779/400000000000 : ℝ)^3615 := by
    have hnat : (1784224813 : ℕ)^4639*400000000000^3615 ≤ 43799791779^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784224813 10000000000 43799791779 400000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425822593/10000000000 : ℝ)^4639 ≤ (11407466762543/25000000000000 : ℝ)^3615 := by
    have hnat : (5425822593 : ℕ)^4639*25000000000000^3615 ≤ 11407466762543^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425822593 10000000000 11407466762543 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219953159/10000000000 : ℝ)^4639 ≤ (2713761561569/6250000000000 : ℝ)^3615 := by
    have hnat : (5219953159 : ℕ)^4639*6250000000000^3615 ≤ 2713761561569^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219953159 10000000000 2713761561569 6250000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784224813/10000000000 : ℝ), (5425822593/10000000000 : ℝ), (5219953159/10000000000 : ℝ)] ![(43799791779/400000000000 : ℝ), (11407466762543/25000000000000 : ℝ), (2713761561569/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784224813/10000000000 : ℝ)|^4639 ≤ (43799791779/400000000000 : ℝ)^3615
        have hw : |(-1784224813/10000000000 : ℝ)|=(1784224813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425822593/10000000000 : ℝ)|^4639 ≤ (11407466762543/25000000000000 : ℝ)^3615
        have hw : |(5425822593/10000000000 : ℝ)|=(5425822593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219953159/10000000000 : ℝ)|^4639 ≤ (2713761561569/6250000000000 : ℝ)^3615
        have hw : |(5219953159/10000000000 : ℝ)|=(5219953159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348171773/10000000000 : ℝ)*x 0 + (-1889546223/10000000000 : ℝ)*x 1 + (5219953167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348171773/10000000000 : ℝ)^4639 ≤ (44793568177037/100000000000000 : ℝ)^3615 := by
    have hnat : (5348171773 : ℕ)^4639*100000000000000^3615 ≤ 44793568177037^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348171773 10000000000 44793568177037 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889546223/10000000000 : ℝ)^4639 ≤ (2357249349097/20000000000000 : ℝ)^3615 := by
    have hnat : (1889546223 : ℕ)^4639*20000000000000^3615 ≤ 2357249349097^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889546223 10000000000 2357249349097 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219953167/10000000000 : ℝ)^4639 ≤ (43420185070499/100000000000000 : ℝ)^3615 := by
    have hnat : (5219953167 : ℕ)^4639*100000000000000^3615 ≤ 43420185070499^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219953167 10000000000 43420185070499 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348171773/10000000000 : ℝ), (-1889546223/10000000000 : ℝ), (5219953167/10000000000 : ℝ)] ![(44793568177037/100000000000000 : ℝ), (2357249349097/20000000000000 : ℝ), (43420185070499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348171773/10000000000 : ℝ)|^4639 ≤ (44793568177037/100000000000000 : ℝ)^3615
        have hw : |(5348171773/10000000000 : ℝ)|=(5348171773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889546223/10000000000 : ℝ)|^4639 ≤ (2357249349097/20000000000000 : ℝ)^3615
        have hw : |(-1889546223/10000000000 : ℝ)|=(1889546223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219953167/10000000000 : ℝ)|^4639 ≤ (43420185070499/100000000000000 : ℝ)^3615
        have hw : |(5219953167/10000000000 : ℝ)|=(5219953167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674085887/5000000000 : ℝ)*x 0 + (1043990633/2000000000 : ℝ)*x 1 + (-1889546223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674085887/5000000000 : ℝ)^4639 ≤ (8958713637557/20000000000000 : ℝ)^3615 := by
    have hnat : (2674085887 : ℕ)^4639*20000000000000^3615 ≤ 8958713637557^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674085887 5000000000 8958713637557 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043990633/2000000000 : ℝ)^4639 ≤ (868403700983/2000000000000 : ℝ)^3615 := by
    have hnat : (1043990633 : ℕ)^4639*2000000000000^3615 ≤ 868403700983^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043990633 2000000000 868403700983 2000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889546223/10000000000 : ℝ)^4639 ≤ (2357249349097/20000000000000 : ℝ)^3615 := by
    have hnat : (1889546223 : ℕ)^4639*20000000000000^3615 ≤ 2357249349097^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889546223 10000000000 2357249349097 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674085887/5000000000 : ℝ), (1043990633/2000000000 : ℝ), (-1889546223/10000000000 : ℝ)] ![(8958713637557/20000000000000 : ℝ), (868403700983/2000000000000 : ℝ), (2357249349097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674085887/5000000000 : ℝ)|^4639 ≤ (8958713637557/20000000000000 : ℝ)^3615
        have hw : |(2674085887/5000000000 : ℝ)|=(2674085887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043990633/2000000000 : ℝ)|^4639 ≤ (868403700983/2000000000000 : ℝ)^3615
        have hw : |(1043990633/2000000000 : ℝ)|=(1043990633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889546223/10000000000 : ℝ)|^4639 ≤ (2357249349097/20000000000000 : ℝ)^3615
        have hw : |(-1889546223/10000000000 : ℝ)|=(1889546223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243050633/10000000000 : ℝ)*x 0 + (801107823/2000000000 : ℝ)*x 1 + (1122959429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243050633/10000000000 : ℝ)^4639 ≤ (4160282319067/12500000000000 : ℝ)^3615 := by
    have hnat : (4243050633 : ℕ)^4639*12500000000000^3615 ≤ 4160282319067^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243050633 10000000000 4160282319067 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801107823/2000000000 : ℝ)^4639 ≤ (15455358028067/50000000000000 : ℝ)^3615 := by
    have hnat : (801107823 : ℕ)^4639*50000000000000^3615 ≤ 15455358028067^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801107823 2000000000 15455358028067 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122959429/2500000000 : ℝ)^4639 ≤ (8951756344541/25000000000000 : ℝ)^3615 := by
    have hnat : (1122959429 : ℕ)^4639*25000000000000^3615 ≤ 8951756344541^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122959429 2500000000 8951756344541 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243050633/10000000000 : ℝ), (801107823/2000000000 : ℝ), (1122959429/2500000000 : ℝ)] ![(4160282319067/12500000000000 : ℝ), (15455358028067/50000000000000 : ℝ), (8951756344541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243050633/10000000000 : ℝ)|^4639 ≤ (4160282319067/12500000000000 : ℝ)^3615
        have hw : |(4243050633/10000000000 : ℝ)|=(4243050633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801107823/2000000000 : ℝ)|^4639 ≤ (15455358028067/50000000000000 : ℝ)^3615
        have hw : |(801107823/2000000000 : ℝ)|=(801107823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122959429/2500000000 : ℝ)|^4639 ≤ (8951756344541/25000000000000 : ℝ)^3615
        have hw : |(1122959429/2500000000 : ℝ)|=(1122959429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111515729/625000000 : ℝ)*x 0 + (5221027277/10000000000 : ℝ)*x 1 + (1356185131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111515729/625000000 : ℝ)^4639 ≤ (10950159410453/100000000000000 : ℝ)^3615 := by
    have hnat : (111515729 : ℕ)^4639*100000000000000^3615 ≤ 10950159410453^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111515729 625000000 10950159410453 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221027277/10000000000 : ℝ)^4639 ≤ (21715825411337/50000000000000 : ℝ)^3615 := by
    have hnat : (5221027277 : ℕ)^4639*50000000000000^3615 ≤ 21715825411337^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221027277 10000000000 21715825411337 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356185131/2500000000 : ℝ)^4639 ≤ (356392107437/781250000000 : ℝ)^3615 := by
    have hnat : (1356185131 : ℕ)^4639*781250000000^3615 ≤ 356392107437^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356185131 2500000000 356392107437 781250000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111515729/625000000 : ℝ), (5221027277/10000000000 : ℝ), (1356185131/2500000000 : ℝ)] ![(10950159410453/100000000000000 : ℝ), (21715825411337/50000000000000 : ℝ), (356392107437/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111515729/625000000 : ℝ)|^4639 ≤ (10950159410453/100000000000000 : ℝ)^3615
        have hw : |(-111515729/625000000 : ℝ)|=(111515729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221027277/10000000000 : ℝ)|^4639 ≤ (21715825411337/50000000000000 : ℝ)^3615
        have hw : |(5221027277/10000000000 : ℝ)|=(5221027277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356185131/2500000000 : ℝ)|^4639 ≤ (356392107437/781250000000 : ℝ)^3615
        have hw : |(1356185131/2500000000 : ℝ)|=(1356185131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293698491/10000000000 : ℝ)*x 0 + (-1684758861/10000000000 : ℝ)*x 1 + (1356185131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293698491/10000000000 : ℝ)^4639 ≤ (11052234430823/25000000000000 : ℝ)^3615 := by
    have hnat : (5293698491 : ℕ)^4639*25000000000000^3615 ≤ 11052234430823^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293698491 10000000000 11052234430823 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684758861/10000000000 : ℝ)^4639 ≤ (2543218124487/25000000000000 : ℝ)^3615 := by
    have hnat : (1684758861 : ℕ)^4639*25000000000000^3615 ≤ 2543218124487^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684758861 10000000000 2543218124487 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356185131/2500000000 : ℝ)^4639 ≤ (356392107437/781250000000 : ℝ)^3615 := by
    have hnat : (1356185131 : ℕ)^4639*781250000000^3615 ≤ 356392107437^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356185131 2500000000 356392107437 781250000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293698491/10000000000 : ℝ), (-1684758861/10000000000 : ℝ), (1356185131/2500000000 : ℝ)] ![(11052234430823/25000000000000 : ℝ), (2543218124487/25000000000000 : ℝ), (356392107437/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293698491/10000000000 : ℝ)|^4639 ≤ (11052234430823/25000000000000 : ℝ)^3615
        have hw : |(5293698491/10000000000 : ℝ)|=(5293698491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1684758861/10000000000 : ℝ)|^4639 ≤ (2543218124487/25000000000000 : ℝ)^3615
        have hw : |(-1684758861/10000000000 : ℝ)|=(1684758861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356185131/2500000000 : ℝ)|^4639 ≤ (356392107437/781250000000 : ℝ)^3615
        have hw : |(1356185131/2500000000 : ℝ)|=(1356185131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323424623/2500000000 : ℝ)*x 0 + (1356185131/2500000000 : ℝ)*x 1 + (-1684758861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323424623/2500000000 : ℝ)^4639 ≤ (44208937734009/100000000000000 : ℝ)^3615 := by
    have hnat : (1323424623 : ℕ)^4639*100000000000000^3615 ≤ 44208937734009^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323424623 2500000000 44208937734009 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356185131/2500000000 : ℝ)^4639 ≤ (356392107437/781250000000 : ℝ)^3615 := by
    have hnat : (1356185131 : ℕ)^4639*781250000000^3615 ≤ 356392107437^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356185131 2500000000 356392107437 781250000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684758861/10000000000 : ℝ)^4639 ≤ (2543218124487/25000000000000 : ℝ)^3615 := by
    have hnat : (1684758861 : ℕ)^4639*25000000000000^3615 ≤ 2543218124487^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684758861 10000000000 2543218124487 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323424623/2500000000 : ℝ), (1356185131/2500000000 : ℝ), (-1684758861/10000000000 : ℝ)] ![(44208937734009/100000000000000 : ℝ), (356392107437/781250000000 : ℝ), (2543218124487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323424623/2500000000 : ℝ)|^4639 ≤ (44208937734009/100000000000000 : ℝ)^3615
        have hw : |(1323424623/2500000000 : ℝ)|=(1323424623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356185131/2500000000 : ℝ)|^4639 ≤ (356392107437/781250000000 : ℝ)^3615
        have hw : |(1356185131/2500000000 : ℝ)|=(1356185131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1684758861/10000000000 : ℝ)|^4639 ≤ (2543218124487/25000000000000 : ℝ)^3615
        have hw : |(-1684758861/10000000000 : ℝ)|=(1684758861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s4_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121557031/5000000000 : ℝ)*x 0 + (4489300483/10000000000 : ℝ)*x 1 + (4008095137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121557031/5000000000 : ℝ)^4639 ≤ (3328289702097/10000000000000 : ℝ)^3615 := by
    have hnat : (2121557031 : ℕ)^4639*10000000000000^3615 ≤ 3328289702097^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121557031 5000000000 3328289702097 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489300483/10000000000 : ℝ)^4639 ≤ (35781072480241/100000000000000 : ℝ)^3615 := by
    have hnat : (4489300483 : ℕ)^4639*100000000000000^3615 ≤ 35781072480241^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489300483 10000000000 35781072480241 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008095137/10000000000 : ℝ)^4639 ≤ (30936030476651/100000000000000 : ℝ)^3615 := by
    have hnat : (4008095137 : ℕ)^4639*100000000000000^3615 ≤ 30936030476651^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008095137 10000000000 30936030476651 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121557031/5000000000 : ℝ), (4489300483/10000000000 : ℝ), (4008095137/10000000000 : ℝ)] ![(3328289702097/10000000000000 : ℝ), (35781072480241/100000000000000 : ℝ), (30936030476651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121557031/5000000000 : ℝ)|^4639 ≤ (3328289702097/10000000000000 : ℝ)^3615
        have hw : |(2121557031/5000000000 : ℝ)|=(2121557031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489300483/10000000000 : ℝ)|^4639 ≤ (35781072480241/100000000000000 : ℝ)^3615
        have hw : |(4489300483/10000000000 : ℝ)|=(4489300483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008095137/10000000000 : ℝ)|^4639 ≤ (30936030476651/100000000000000 : ℝ)^3615
        have hw : |(4008095137/10000000000 : ℝ)|=(4008095137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11093/100000 : ℝ) ^ (4637/1024 : ℝ) ≤ (4738883673230041/100000000000000000000 : ℝ) := by
    have hpowers : (11093/100000 : ℝ)^4637 ≤ (4738883673230041/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11093 : ℕ)^4637*100000000000000000000^1024 ≤ 4738883673230041^1024*100000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11093 100000 4738883673230041 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11093/100000 : ℝ)) (X := (4738883673230041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15519/100000 : ℝ) ^ (4637/1024 : ℝ) ≤ (21675633897444231/100000000000000000000 : ℝ) := by
    have hpowers : (15519/100000 : ℝ)^4637 ≤ (21675633897444231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15519 : ℕ)^4637*100000000000000000000^1024 ≤ 21675633897444231^1024*100000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15519 100000 21675633897444231 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15519/100000 : ℝ)) (X := (21675633897444231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004738883673230041/50000000000000000000 : ℝ) ≤ (2500052323029051/2500000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50004738883673230041/50000000000000000000 : ℝ)^1024 ≤ (2500052323029051/2500000000000000 : ℝ)^4637 := by
      have hnat : (50004738883673230041 : ℕ)^1024*2500000000000000^4637 ≤ 2500052323029051^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004738883673230041 50000000000000000000 2500052323029051 2500000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500052323029051/2500000000000000 : ℝ)) (X := (50004738883673230041/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125825453674083571/3125000000000000000 : ℝ) ≤ (10000583258204887/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (3125825453674083571/3125000000000000000 : ℝ)^1024 ≤ (10000583258204887/10000000000000000 : ℝ)^4637 := by
      have hnat : (3125825453674083571 : ℕ)^1024*10000000000000000^4637 ≤ 10000583258204887^4637*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125825453674083571 3125000000000000000 10000583258204887 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000583258204887/10000000000000000 : ℝ)) (X := (3125825453674083571/3125000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021675633897444231/50000000000000000000 : ℝ) ≤ (1000095722429357/1000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50021675633897444231/50000000000000000000 : ℝ)^1024 ≤ (1000095722429357/1000000000000000 : ℝ)^4637 := by
      have hnat : (50021675633897444231 : ℕ)^1024*1000000000000000^4637 ≤ 1000095722429357^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021675633897444231 50000000000000000000 1000095722429357 1000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000095722429357/1000000000000000 : ℝ)) (X := (50021675633897444231/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4738883673230041/100000000000000000000 : ℝ) ≤ ((22126314757631398933/22130000000000000000 : ℝ)+2*(373966088683/442600000000000 : ℝ)*(11093/100000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (22126314757631398933/22130000000000000000 : ℝ)+2*(373966088683/442600000000000 : ℝ)*(11093/100000 : ℝ)=(2500052323029051/2500000000000000 : ℝ) by norm_num, show 1+2*(4738883673230041/100000000000000000000 : ℝ)=(50004738883673230041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21675633897444231/100000000000000000000 : ℝ)+(4738883673230041/100000000000000000000 : ℝ) ≤ ((22126314757631398933/22130000000000000000 : ℝ)+(373966088683/442600000000000 : ℝ)*((15519/100000 : ℝ)+(11093/100000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (22126314757631398933/22130000000000000000 : ℝ)+(373966088683/442600000000000 : ℝ)*((15519/100000 : ℝ)+(11093/100000 : ℝ))=(10000583258204887/10000000000000000 : ℝ) by norm_num, show 1+(21675633897444231/100000000000000000000 : ℝ)+(4738883673230041/100000000000000000000 : ℝ)=(3125825453674083571/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21675633897444231/100000000000000000000 : ℝ) ≤ ((22126314757631398933/22130000000000000000 : ℝ)+2*(373966088683/442600000000000 : ℝ)*(15519/100000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (22126314757631398933/22130000000000000000 : ℝ)+2*(373966088683/442600000000000 : ℝ)*(15519/100000 : ℝ)=(1000095722429357/1000000000000000 : ℝ) by norm_num, show 1+2*(21675633897444231/100000000000000000000 : ℝ)=(50021675633897444231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22126314757631398933/22130000000000000000 : ℝ)*(X 1 0+X 2 0)+(373966088683/442600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (22126314757631398933/22130000000000000000 : ℝ)) (alpha := (373966088683/442600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22126314757631398933/22130000000000000000 : ℝ)*(X 0 1+X 2 1)+(373966088683/442600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (22126314757631398933/22130000000000000000 : ℝ)) (alpha := (373966088683/442600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22126314757631398933/22130000000000000000 : ℝ)*(X 0 2+X 1 2)+(373966088683/442600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (22126314757631398933/22130000000000000000 : ℝ)) (alpha := (373966088683/442600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1784224813/10000000000 : ℝ)*X 0 0+(5425822593/10000000000 : ℝ)*X 0 1+(5219953159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348171773/10000000000 : ℝ)*X 1 0+(-1889546223/10000000000 : ℝ)*X 1 1+(5219953167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674085887/5000000000 : ℝ)*X 2 0+(1043990633/2000000000 : ℝ)*X 2 1+(-1889546223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243050633/10000000000 : ℝ)*X 0 0+(801107823/2000000000 : ℝ)*X 0 1+(1122959429/2500000000 : ℝ)*X 0 2+(4243050633/10000000000 : ℝ)*X 1 0+(801107823/2000000000 : ℝ)*X 1 1+(1122959429/2500000000 : ℝ)*X 1 2+(4243050633/10000000000 : ℝ)*X 2 0+(801107823/2000000000 : ℝ)*X 2 1+(1122959429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-111515729/625000000 : ℝ)*X 0 0+(5221027277/10000000000 : ℝ)*X 0 1+(1356185131/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293698491/10000000000 : ℝ)*X 1 0+(-1684758861/10000000000 : ℝ)*X 1 1+(1356185131/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323424623/2500000000 : ℝ)*X 2 0+(1356185131/2500000000 : ℝ)*X 2 1+(-1684758861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121557031/5000000000 : ℝ)*X 0 0+(4489300483/10000000000 : ℝ)*X 0 1+(4008095137/10000000000 : ℝ)*X 0 2+(2121557031/5000000000 : ℝ)*X 1 0+(4489300483/10000000000 : ℝ)*X 1 1+(4008095137/10000000000 : ℝ)*X 1 2+(2121557031/5000000000 : ℝ)*X 2 0+(4489300483/10000000000 : ℝ)*X 2 1+(4008095137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27748704854055702908211/2213000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2117201841/100000000000000 : ℝ)*(base19) + (61887801/3125000000000 : ℝ)*(base23) + (36822287/50000000000000 : ℝ)*(lower2) + (38738021/12500000000000 : ℝ)*(upper3) + (210429791/100000000000000 : ℝ)*(upper5) + (172847443726807/5000000000000 : ℝ)*(major0) + (172847443726807/5000000000000 : ℝ)*(major1) + (172847443726807/5000000000000 : ℝ)*(major2) + (4857483380788129/100000000000000 : ℝ)*(sp0) + (607189467383119/12500000000000 : ℝ)*(sp1) + (4857515875857161/100000000000000 : ℝ)*(sp2) + (514090941592119/25000000000000 : ℝ)*(sp3) + (4309434833/12500000000000 : ℝ)*(sp4) + (15708471873/100000000000000 : ℝ)*(sp7) + (514094868710087/25000000000000 : ℝ)*(f.failure) + (4857517856266793/100000000000000 : ℝ)*(f.sum) + (12415867665431/2213000000000000000000000000 : ℝ)*base66 + (994780987716746931/110650000000000000000000000000000 : ℝ)*base67 + (68640980009253069/110650000000000000000000000000000 : ℝ)*base70 + (279923997722153069/110650000000000000000000000000000 : ℝ)*base72 + (3509333021423/2213000000000000000000000000 : ℝ)*base73 + (1587825643121696931/110650000000000000000000000000000 : ℝ)*base75 + (1034111489618853069/110650000000000000000000000000000 : ℝ)*base78 + (1016916726025746931/110650000000000000000000000000000 : ℝ)*base79 + (249710027103/55325000000000000000000000 : ℝ)*base82 + (21169717/2500000000000000000000 : ℝ)*base90 + (21169717/2500000000000000000000 : ℝ)*base92 + (21169717/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5484053058772888301742005649/553250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194769177/12500000000000 : ℝ)*(base19) + (1687990537/100000000000000 : ℝ)*(base23) + (204193669/100000000000000 : ℝ)*(upper3) + (2339987/4000000000000 : ℝ)*(lower4) + (206023501/100000000000000 : ℝ)*(upper5) + (1746743698196283/50000000000000 : ℝ)*(major0) + (1746743698196283/50000000000000 : ℝ)*(major1) + (1746743698196283/50000000000000 : ℝ)*(major2) + (6210123969/25000000000000 : ℝ)*(sp1) + (3328595803/12500000000000 : ℝ)*(sp2) + (4908859905782413/100000000000000 : ℝ)*(sp4) + (4908833507133121/100000000000000 : ℝ)*(sp5) + (4908831589025451/100000000000000 : ℝ)*(sp6) + (519528639147077/25000000000000 : ℝ)*(sp7) + (519528639147077/25000000000000 : ℝ)*(f.failure) + (4908859905782413/100000000000000 : ℝ)*(f.sum) + (29076942340129/11065000000000000000000000000 : ℝ)*base65 + (1129074745802716039/1106500000000000000000000000000000 : ℝ)*base67 + (12975562010623216039/1106500000000000000000000000000000 : ℝ)*base69 + (217115714117716039/1106500000000000000000000000000000 : ℝ)*base71 + (20735206600007/5532500000000000000000000000 : ℝ)*base73 + (18950296551377216039/1106500000000000000000000000000000 : ℝ)*base75 + (3244380755409216039/1106500000000000000000000000000000 : ℝ)*base77 + (18377496736763216039/1106500000000000000000000000000000 : ℝ)*base79 + (9321050432661/2766250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3821807/2500000000000000000000 : ℝ)*base90 + (3821807/2500000000000000000000 : ℝ)*base92 + (3821807/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1571_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1571_s5_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-446061987/2500000000 : ℝ)*x 0 + (2712836777/5000000000 : ℝ)*x 1 + (5220086771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446061987/2500000000 : ℝ)^4639 ≤ (10950130144951/100000000000000 : ℝ)^3615 := by
    have hnat : (446061987 : ℕ)^4639*100000000000000^3615 ≤ 10950130144951^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446061987 2500000000 10950130144951 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712836777/5000000000 : ℝ)^4639 ≤ (22814129317941/50000000000000 : ℝ)^3615 := by
    have hnat : (2712836777 : ℕ)^4639*50000000000000^3615 ≤ 22814129317941^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712836777 5000000000 22814129317941 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220086771/10000000000 : ℝ)^4639 ≤ (43421611210527/100000000000000 : ℝ)^3615 := by
    have hnat : (5220086771 : ℕ)^4639*100000000000000^3615 ≤ 43421611210527^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220086771 10000000000 43421611210527 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446061987/2500000000 : ℝ), (2712836777/5000000000 : ℝ), (5220086771/10000000000 : ℝ)] ![(10950130144951/100000000000000 : ℝ), (22814129317941/50000000000000 : ℝ), (43421611210527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446061987/2500000000 : ℝ)|^4639 ≤ (10950130144951/100000000000000 : ℝ)^3615
        have hw : |(-446061987/2500000000 : ℝ)|=(446061987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712836777/5000000000 : ℝ)|^4639 ≤ (22814129317941/50000000000000 : ℝ)^3615
        have hw : |(2712836777/5000000000 : ℝ)|=(2712836777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220086771/10000000000 : ℝ)|^4639 ≤ (43421611210527/100000000000000 : ℝ)^3615
        have hw : |(5220086771/10000000000 : ℝ)|=(5220086771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534813217/1000000000 : ℝ)*x 0 + (-472355493/2500000000 : ℝ)*x 1 + (2610043107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534813217/1000000000 : ℝ)^4639 ≤ (44793142525689/100000000000000 : ℝ)^3615 := by
    have hnat : (534813217 : ℕ)^4639*100000000000000^3615 ≤ 44793142525689^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534813217 1000000000 44793142525689 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472355493/2500000000 : ℝ)^4639 ≤ (2357050437583/20000000000000 : ℝ)^3615 := by
    have hnat : (472355493 : ℕ)^4639*20000000000000^3615 ≤ 2357050437583^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472355493 2500000000 2357050437583 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610043107/5000000000 : ℝ)^4639 ≤ (347372842119/800000000000 : ℝ)^3615 := by
    have hnat : (2610043107 : ℕ)^4639*800000000000^3615 ≤ 347372842119^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610043107 5000000000 347372842119 800000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534813217/1000000000 : ℝ), (-472355493/2500000000 : ℝ), (2610043107/5000000000 : ℝ)] ![(44793142525689/100000000000000 : ℝ), (2357050437583/20000000000000 : ℝ), (347372842119/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534813217/1000000000 : ℝ)|^4639 ≤ (44793142525689/100000000000000 : ℝ)^3615
        have hw : |(534813217/1000000000 : ℝ)|=(534813217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472355493/2500000000 : ℝ)|^4639 ≤ (2357050437583/20000000000000 : ℝ)^3615
        have hw : |(-472355493/2500000000 : ℝ)|=(472355493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610043107/5000000000 : ℝ)|^4639 ≤ (347372842119/800000000000 : ℝ)^3615
        have hw : |(2610043107/5000000000 : ℝ)|=(2610043107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348131739/10000000000 : ℝ)*x 0 + (1305021683/2500000000 : ℝ)*x 1 + (-94471093/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348131739/10000000000 : ℝ)^4639 ≤ (1791725515733/4000000000000 : ℝ)^3615 := by
    have hnat : (5348131739 : ℕ)^4639*4000000000000^3615 ≤ 1791725515733^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348131739 10000000000 1791725515733 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305021683/2500000000 : ℝ)^4639 ≤ (1736864431769/4000000000000 : ℝ)^3615 := by
    have hnat : (1305021683 : ℕ)^4639*4000000000000^3615 ≤ 1736864431769^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305021683 2500000000 1736864431769 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94471093/500000000 : ℝ)^4639 ≤ (2946312822857/25000000000000 : ℝ)^3615 := by
    have hnat : (94471093 : ℕ)^4639*25000000000000^3615 ≤ 2946312822857^3615*500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94471093 500000000 2946312822857 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348131739/10000000000 : ℝ), (1305021683/2500000000 : ℝ), (-94471093/500000000 : ℝ)] ![(1791725515733/4000000000000 : ℝ), (1736864431769/4000000000000 : ℝ), (2946312822857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348131739/10000000000 : ℝ)|^4639 ≤ (1791725515733/4000000000000 : ℝ)^3615
        have hw : |(5348131739/10000000000 : ℝ)|=(5348131739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305021683/2500000000 : ℝ)|^4639 ≤ (1736864431769/4000000000000 : ℝ)^3615
        have hw : |(1305021683/2500000000 : ℝ)|=(1305021683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94471093/500000000 : ℝ)|^4639 ≤ (2946312822857/25000000000000 : ℝ)^3615
        have hw : |(-94471093/500000000 : ℝ)|=(94471093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121532033/5000000000 : ℝ)*x 0 + (4005871037/10000000000 : ℝ)*x 1 + (4491503169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121532033/5000000000 : ℝ)^4639 ≤ (33282393767219/100000000000000 : ℝ)^3615 := by
    have hnat : (2121532033 : ℕ)^4639*100000000000000^3615 ≤ 33282393767219^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121532033 5000000000 33282393767219 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005871037/10000000000 : ℝ)^4639 ≤ (30914003098451/100000000000000 : ℝ)^3615 := by
    have hnat : (4005871037 : ℕ)^4639*100000000000000^3615 ≤ 30914003098451^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005871037 10000000000 30914003098451 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491503169/10000000000 : ℝ)^4639 ≤ (35803603119623/100000000000000 : ℝ)^3615 := by
    have hnat : (4491503169 : ℕ)^4639*100000000000000^3615 ≤ 35803603119623^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491503169 10000000000 35803603119623 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121532033/5000000000 : ℝ), (4005871037/10000000000 : ℝ), (4491503169/10000000000 : ℝ)] ![(33282393767219/100000000000000 : ℝ), (30914003098451/100000000000000 : ℝ), (35803603119623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121532033/5000000000 : ℝ)|^4639 ≤ (33282393767219/100000000000000 : ℝ)^3615
        have hw : |(2121532033/5000000000 : ℝ)|=(2121532033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005871037/10000000000 : ℝ)|^4639 ≤ (30914003098451/100000000000000 : ℝ)^3615
        have hw : |(4005871037/10000000000 : ℝ)|=(4005871037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491503169/10000000000 : ℝ)|^4639 ≤ (35803603119623/100000000000000 : ℝ)^3615
        have hw : |(4491503169/10000000000 : ℝ)|=(4491503169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784274711/10000000000 : ℝ)*x 0 + (5221157687/10000000000 : ℝ)*x 1 + (54245947/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784274711/10000000000 : ℝ)^4639 ≤ (10950340918381/100000000000000 : ℝ)^3615 := by
    have hnat : (1784274711 : ℕ)^4639*100000000000000^3615 ≤ 10950340918381^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784274711 10000000000 10950340918381 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221157687/10000000000 : ℝ)^4639 ≤ (2171652147487/5000000000000 : ℝ)^3615 := by
    have hnat : (5221157687 : ℕ)^4639*5000000000000^3615 ≤ 2171652147487^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221157687 10000000000 2171652147487 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54245947/100000000 : ℝ)^4639 ≤ (45616616122387/100000000000000 : ℝ)^3615 := by
    have hnat : (54245947 : ℕ)^4639*100000000000000^3615 ≤ 45616616122387^3615*100000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54245947 100000000 45616616122387 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784274711/10000000000 : ℝ), (5221157687/10000000000 : ℝ), (54245947/100000000 : ℝ)] ![(10950340918381/100000000000000 : ℝ), (2171652147487/5000000000000 : ℝ), (45616616122387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784274711/10000000000 : ℝ)|^4639 ≤ (10950340918381/100000000000000 : ℝ)^3615
        have hw : |(-1784274711/10000000000 : ℝ)|=(1784274711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221157687/10000000000 : ℝ)|^4639 ≤ (2171652147487/5000000000000 : ℝ)^3615
        have hw : |(5221157687/10000000000 : ℝ)|=(5221157687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54245947/100000000 : ℝ)|^4639 ≤ (45616616122387/100000000000000 : ℝ)^3615
        have hw : |(54245947/100000000 : ℝ)|=(54245947/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330858341/625000000 : ℝ)*x 0 + (-1684913591/10000000000 : ℝ)*x 1 + (2712297349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330858341/625000000 : ℝ)^4639 ≤ (44209312438127/100000000000000 : ℝ)^3615 := by
    have hnat : (330858341 : ℕ)^4639*100000000000000^3615 ≤ 44209312438127^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330858341 625000000 44209312438127 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684913591/10000000000 : ℝ)^4639 ≤ (5087035725389/50000000000000 : ℝ)^3615 := by
    have hnat : (1684913591 : ℕ)^4639*50000000000000^3615 ≤ 5087035725389^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684913591 10000000000 5087035725389 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712297349/5000000000 : ℝ)^4639 ≤ (9123323220161/20000000000000 : ℝ)^3615 := by
    have hnat : (2712297349 : ℕ)^4639*20000000000000^3615 ≤ 9123323220161^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712297349 5000000000 9123323220161 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330858341/625000000 : ℝ), (-1684913591/10000000000 : ℝ), (2712297349/5000000000 : ℝ)] ![(44209312438127/100000000000000 : ℝ), (5087035725389/50000000000000 : ℝ), (9123323220161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330858341/625000000 : ℝ)|^4639 ≤ (44209312438127/100000000000000 : ℝ)^3615
        have hw : |(330858341/625000000 : ℝ)|=(330858341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1684913591/10000000000 : ℝ)|^4639 ≤ (5087035725389/50000000000000 : ℝ)^3615
        have hw : |(-1684913591/10000000000 : ℝ)|=(1684913591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712297349/5000000000 : ℝ)|^4639 ≤ (9123323220161/20000000000000 : ℝ)^3615
        have hw : |(2712297349/5000000000 : ℝ)|=(2712297349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330858341/625000000 : ℝ)*x 0 + (2712297349/5000000000 : ℝ)*x 1 + (-1684913591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330858341/625000000 : ℝ)^4639 ≤ (44209312438127/100000000000000 : ℝ)^3615 := by
    have hnat : (330858341 : ℕ)^4639*100000000000000^3615 ≤ 44209312438127^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330858341 625000000 44209312438127 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712297349/5000000000 : ℝ)^4639 ≤ (9123323220161/20000000000000 : ℝ)^3615 := by
    have hnat : (2712297349 : ℕ)^4639*20000000000000^3615 ≤ 9123323220161^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712297349 5000000000 9123323220161 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684913591/10000000000 : ℝ)^4639 ≤ (5087035725389/50000000000000 : ℝ)^3615 := by
    have hnat : (1684913591 : ℕ)^4639*50000000000000^3615 ≤ 5087035725389^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684913591 10000000000 5087035725389 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330858341/625000000 : ℝ), (2712297349/5000000000 : ℝ), (-1684913591/10000000000 : ℝ)] ![(44209312438127/100000000000000 : ℝ), (9123323220161/20000000000000 : ℝ), (5087035725389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330858341/625000000 : ℝ)|^4639 ≤ (44209312438127/100000000000000 : ℝ)^3615
        have hw : |(330858341/625000000 : ℝ)|=(330858341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712297349/5000000000 : ℝ)|^4639 ≤ (9123323220161/20000000000000 : ℝ)^3615
        have hw : |(2712297349/5000000000 : ℝ)|=(2712297349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1684913591/10000000000 : ℝ)|^4639 ≤ (5087035725389/50000000000000 : ℝ)^3615
        have hw : |(-1684913591/10000000000 : ℝ)|=(1684913591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s5_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530390961/1250000000 : ℝ)*x 0 + (4488972653/10000000000 : ℝ)*x 1 + (1002104953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530390961/1250000000 : ℝ)^4639 ≤ (16641517089473/50000000000000 : ℝ)^3615 := by
    have hnat : (530390961 : ℕ)^4639*50000000000000^3615 ≤ 16641517089473^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530390961 1250000000 16641517089473 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488972653/10000000000 : ℝ)^4639 ≤ (4472214933681/12500000000000 : ℝ)^3615 := by
    have hnat : (4488972653 : ℕ)^4639*12500000000000^3615 ≤ 4472214933681^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488972653 10000000000 4472214933681 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002104953/2500000000 : ℝ)^4639 ≤ (30939246331721/100000000000000 : ℝ)^3615 := by
    have hnat : (1002104953 : ℕ)^4639*100000000000000^3615 ≤ 30939246331721^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002104953 2500000000 30939246331721 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530390961/1250000000 : ℝ), (4488972653/10000000000 : ℝ), (1002104953/2500000000 : ℝ)] ![(16641517089473/50000000000000 : ℝ), (4472214933681/12500000000000 : ℝ), (30939246331721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530390961/1250000000 : ℝ)|^4639 ≤ (16641517089473/50000000000000 : ℝ)^3615
        have hw : |(530390961/1250000000 : ℝ)|=(530390961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488972653/10000000000 : ℝ)|^4639 ≤ (4472214933681/12500000000000 : ℝ)^3615
        have hw : |(4488972653/10000000000 : ℝ)|=(4488972653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002104953/2500000000 : ℝ)|^4639 ≤ (30939246331721/100000000000000 : ℝ)^3615
        have hw : |(1002104953/2500000000 : ℝ)|=(1002104953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2781/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4637/1024 : ℝ) ≤ (2396645406817421/50000000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4637 ≤ (2396645406817421/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4637*50000000000000000000^1024 ≤ 2396645406817421^1024*100000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 2396645406817421 50000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (2396645406817421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4637/1024 : ℝ) ≤ (21480255594177719/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4637 ≤ (21480255594177719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4637*100000000000000000000^1024 ≤ 21480255594177719^1024*3125^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 21480255594177719 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (21480255594177719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002396645406817421/25000000000000000000 : ℝ) ≤ (2500052923727501/2500000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (25002396645406817421/25000000000000000000 : ℝ)^1024 ≤ (2500052923727501/2500000000000000 : ℝ)^4637 := by
      have hnat : (25002396645406817421 : ℕ)^1024*2500000000000000^4637 ≤ 2500052923727501^4637*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002396645406817421 25000000000000000000 2500052923727501 2500000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500052923727501/2500000000000000 : ℝ)) (X := (25002396645406817421/25000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026273546407812561/100000000000000000000 : ℝ) ≤ (10000580145743233/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (100026273546407812561/100000000000000000000 : ℝ)^1024 ≤ (10000580145743233/10000000000000000 : ℝ)^4637 := by
      have hnat : (100026273546407812561 : ℕ)^1024*10000000000000000^4637 ≤ 10000580145743233^4637*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026273546407812561 100000000000000000000 10000580145743233 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000580145743233/10000000000000000 : ℝ)) (X := (100026273546407812561/100000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021480255594177719/50000000000000000000 : ℝ) ≤ (5000474298288231/5000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50021480255594177719/50000000000000000000 : ℝ)^1024 ≤ (5000474298288231/5000000000000000 : ℝ)^4637 := by
      have hnat : (50021480255594177719 : ℕ)^1024*5000000000000000^4637 ≤ 5000474298288231^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021480255594177719 50000000000000000000 5000474298288231 5000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000474298288231/5000000000000000 : ℝ)) (X := (50021480255594177719/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2396645406817421/50000000000000000000 : ℝ) ≤ ((79386780705889651/79400000000000000 : ℝ)+2*(368450833229/436700000000000 : ℝ)*(11121/100000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (79386780705889651/79400000000000000 : ℝ)+2*(368450833229/436700000000000 : ℝ)*(11121/100000 : ℝ)=(2500052923727501/2500000000000000 : ℝ) by norm_num, show 1+2*(2396645406817421/50000000000000000000 : ℝ)=(25002396645406817421/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21480255594177719/100000000000000000000 : ℝ)+(2396645406817421/50000000000000000000 : ℝ) ≤ ((79386780705889651/79400000000000000 : ℝ)+(368450833229/436700000000000 : ℝ)*((484/3125 : ℝ)+(11121/100000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (79386780705889651/79400000000000000 : ℝ)+(368450833229/436700000000000 : ℝ)*((484/3125 : ℝ)+(11121/100000 : ℝ))=(10000580145743233/10000000000000000 : ℝ) by norm_num, show 1+(21480255594177719/100000000000000000000 : ℝ)+(2396645406817421/50000000000000000000 : ℝ)=(100026273546407812561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21480255594177719/100000000000000000000 : ℝ) ≤ ((79386780705889651/79400000000000000 : ℝ)+2*(368450833229/436700000000000 : ℝ)*(484/3125 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (79386780705889651/79400000000000000 : ℝ)+2*(368450833229/436700000000000 : ℝ)*(484/3125 : ℝ)=(5000474298288231/5000000000000000 : ℝ) by norm_num, show 1+2*(21480255594177719/100000000000000000000 : ℝ)=(50021480255594177719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79386780705889651/79400000000000000 : ℝ)*(X 1 0+X 2 0)+(368450833229/436700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (79386780705889651/79400000000000000 : ℝ)) (alpha := (368450833229/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79386780705889651/79400000000000000 : ℝ)*(X 0 1+X 2 1)+(368450833229/436700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (79386780705889651/79400000000000000 : ℝ)) (alpha := (368450833229/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79386780705889651/79400000000000000 : ℝ)*(X 0 2+X 1 2)+(368450833229/436700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (79386780705889651/79400000000000000 : ℝ)) (alpha := (368450833229/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-446061987/2500000000 : ℝ)*X 0 0+(2712836777/5000000000 : ℝ)*X 0 1+(5220086771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534813217/1000000000 : ℝ)*X 1 0+(-472355493/2500000000 : ℝ)*X 1 1+(2610043107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348131739/10000000000 : ℝ)*X 2 0+(1305021683/2500000000 : ℝ)*X 2 1+(-94471093/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121532033/5000000000 : ℝ)*X 0 0+(4005871037/10000000000 : ℝ)*X 0 1+(4491503169/10000000000 : ℝ)*X 0 2+(2121532033/5000000000 : ℝ)*X 1 0+(4005871037/10000000000 : ℝ)*X 1 1+(4491503169/10000000000 : ℝ)*X 1 2+(2121532033/5000000000 : ℝ)*X 2 0+(4005871037/10000000000 : ℝ)*X 2 1+(4491503169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1784274711/10000000000 : ℝ)*X 0 0+(5221157687/10000000000 : ℝ)*X 0 1+(54245947/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330858341/625000000 : ℝ)*X 1 0+(-1684913591/10000000000 : ℝ)*X 1 1+(2712297349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330858341/625000000 : ℝ)*X 2 0+(2712297349/5000000000 : ℝ)*X 2 1+(-1684913591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530390961/1250000000 : ℝ)*X 0 0+(4488972653/10000000000 : ℝ)*X 0 1+(1002104953/2500000000 : ℝ)*X 0 2+(530390961/1250000000 : ℝ)*X 1 0+(4488972653/10000000000 : ℝ)*X 1 1+(1002104953/2500000000 : ℝ)*X 1 2+(530390961/1250000000 : ℝ)*X 2 0+(4488972653/10000000000 : ℝ)*X 2 1+(1002104953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130087252232912148724137/10917500000000000000000000000 : ℝ) := by norm_num
    linear_combination (893567219/50000000000000 : ℝ)*(base19) + (1372672319/100000000000000 : ℝ)*(base23) + (345601/200000000000 : ℝ)*(upper3) + (12014297/100000000000000 : ℝ)*(upper4) + (10526413/5000000000000 : ℝ)*(upper5) + (432710074733641/12500000000000 : ℝ)*(major0) + (432710074733641/12500000000000 : ℝ)*(major1) + (432710074733641/12500000000000 : ℝ)*(major2) + (4864146567114177/100000000000000 : ℝ)*(sp0) + (608020606570553/12500000000000 : ℝ)*(sp1) + (304010329189159/6250000000000 : ℝ)*(sp2) + (1029591783350021/50000000000000 : ℝ)*(sp3) + (10036292343/50000000000000 : ℝ)*(sp4) + (10592156681/100000000000000 : ℝ)*(sp7) + (2059194158856723/100000000000000 : ℝ)*(f.failure) + (4864166639698863/100000000000000 : ℝ)*(f.sum) + (24689550019191/10917500000000000000000000000 : ℝ)*base65 + (53335942667052299/10917500000000000000000000000000 : ℝ)*base68 + (18552014162177299/10917500000000000000000000000000 : ℝ)*base70 + (29957315082129799/10917500000000000000000000000000 : ℝ)*base72 + (16061800284053/21835000000000000000000000000 : ℝ)*base74 + (87476190389515201/10917500000000000000000000000000 : ℝ)*base75 + (1376347316590201/10917500000000000000000000000000 : ℝ)*base77 + (144145716059057701/10917500000000000000000000000000 : ℝ)*base79 + (56965987278631/10917500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (48156007/10000000000000000000000 : ℝ)*base89 + (48156007/10000000000000000000000 : ℝ)*base91 + (48156007/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11027028473026913021011839/992500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174332397/10000000000000 : ℝ)*(base19) + (1889395757/100000000000000 : ℝ)*(base23) + (141940961/25000000000000 : ℝ)*(lower1) + (7152951/3125000000000 : ℝ)*(upper3) + (66220869/100000000000000 : ℝ)*(lower4) + (9183173/4000000000000 : ℝ)*(upper5) + (874552755877663/25000000000000 : ℝ)*(major0) + (874552755877663/25000000000000 : ℝ)*(major1) + (874552755877663/25000000000000 : ℝ)*(major2) + (1020770689/50000000000000 : ℝ)*(sp2) + (4915497252136303/100000000000000 : ℝ)*(sp4) + (4915495508812333/100000000000000 : ℝ)*(sp5) + (76804583143737/1562500000000 : ℝ)*(sp6) + (2080924424539779/100000000000000 : ℝ)*(sp7) + (2080924424539779/100000000000000 : ℝ)*(f.failure) + (4915497252136303/100000000000000 : ℝ)*(f.sum) + (32088192277943/21835000000000000000000000000 : ℝ)*base65 + (697625993707004257/21835000000000000000000000000000 : ℝ)*base68 + (98729517375004257/21835000000000000000000000000000 : ℝ)*base70 + (1888330880723924257/21835000000000000000000000000000 : ℝ)*base72 + (4551512165229/2729375000000000000000000000 : ℝ)*base74 + (317501996972105743/21835000000000000000000000000000 : ℝ)*base75 + (355886126031094257/21835000000000000000000000000000 : ℝ)*base78 + (125959707186830743/21835000000000000000000000000000 : ℝ)*base79 + (1152156989297/341171875000000000000000000 : ℝ)*base81 + (58879511/10000000000000000000000 : ℝ)*base89 + (58879511/10000000000000000000000 : ℝ)*base91 + (58879511/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1571_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1571_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1571_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1571_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1571_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15809/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
