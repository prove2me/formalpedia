-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:13.585875+00:00
-- url     : https://prove2.me/submissions/ad4d8271-2b22-4757-9207-38b9614574c6

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c312060_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-866124709/5000000000 : ℝ)*x 0 + (2195963937/5000000000 : ℝ)*x 1 + (-6229808503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866124709/5000000000 : ℝ)^73 ≤ (10589782353521/100000000000000 : ℝ)^57 := by
    have hnat : (866124709 : ℕ)^73*100000000000000^57 ≤ 10589782353521^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866124709 5000000000 10589782353521 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195963937/5000000000 : ℝ)^73 ≤ (34861645864603/100000000000000 : ℝ)^57 := by
    have hnat : (2195963937 : ℕ)^73*100000000000000^57 ≤ 34861645864603^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195963937 5000000000 34861645864603 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6229808503/10000000000 : ℝ)^73 ≤ (3409285735799/6250000000000 : ℝ)^57 := by
    have hnat : (6229808503 : ℕ)^73*6250000000000^57 ≤ 3409285735799^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6229808503 10000000000 3409285735799 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-866124709/5000000000 : ℝ), (2195963937/5000000000 : ℝ), (-6229808503/10000000000 : ℝ)] ![(10589782353521/100000000000000 : ℝ), (34861645864603/100000000000000 : ℝ), (3409285735799/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-866124709/5000000000 : ℝ)|^73 ≤ (10589782353521/100000000000000 : ℝ)^57
        have hw : |(-866124709/5000000000 : ℝ)|=(866124709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2195963937/5000000000 : ℝ)|^73 ≤ (34861645864603/100000000000000 : ℝ)^57
        have hw : |(2195963937/5000000000 : ℝ)|=(2195963937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6229808503/10000000000 : ℝ)|^73 ≤ (3409285735799/6250000000000 : ℝ)^57
        have hw : |(-6229808503/10000000000 : ℝ)|=(6229808503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4503263337/10000000000 : ℝ)*x 0 + (-1836242641/10000000000 : ℝ)*x 1 + (-1513654193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503263337/10000000000 : ℝ)^73 ≤ (4499682538373/12500000000000 : ℝ)^57 := by
    have hnat : (4503263337 : ℕ)^73*12500000000000^57 ≤ 4499682538373^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503263337 10000000000 4499682538373 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836242641/10000000000 : ℝ)^73 ≤ (2852685901767/25000000000000 : ℝ)^57 := by
    have hnat : (1836242641 : ℕ)^73*25000000000000^57 ≤ 2852685901767^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836242641 10000000000 2852685901767 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513654193/2500000000 : ℝ)^73 ≤ (84146873699/160000000000 : ℝ)^57 := by
    have hnat : (1513654193 : ℕ)^73*160000000000^57 ≤ 84146873699^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513654193 2500000000 84146873699 160000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503263337/10000000000 : ℝ), (-1836242641/10000000000 : ℝ), (-1513654193/2500000000 : ℝ)] ![(4499682538373/12500000000000 : ℝ), (2852685901767/25000000000000 : ℝ), (84146873699/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503263337/10000000000 : ℝ)|^73 ≤ (4499682538373/12500000000000 : ℝ)^57
        have hw : |(4503263337/10000000000 : ℝ)|=(4503263337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1836242641/10000000000 : ℝ)|^73 ≤ (2852685901767/25000000000000 : ℝ)^57
        have hw : |(-1836242641/10000000000 : ℝ)|=(1836242641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1513654193/2500000000 : ℝ)|^73 ≤ (84146873699/160000000000 : ℝ)^57
        have hw : |(-1513654193/2500000000 : ℝ)|=(1513654193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2351190047/5000000000 : ℝ)*x 0 + (6081186487/10000000000 : ℝ)*x 1 + (1534098319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2351190047/5000000000 : ℝ)^73 ≤ (38048430105333/100000000000000 : ℝ)^57 := by
    have hnat : (2351190047 : ℕ)^73*100000000000000^57 ≤ 38048430105333^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351190047 5000000000 38048430105333 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6081186487/10000000000 : ℝ)^73 ≤ (26443775963391/50000000000000 : ℝ)^57 := by
    have hnat : (6081186487 : ℕ)^73*50000000000000^57 ≤ 26443775963391^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6081186487 10000000000 26443775963391 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1534098319/10000000000 : ℝ)^73 ≤ (4532008978977/50000000000000 : ℝ)^57 := by
    have hnat : (1534098319 : ℕ)^73*50000000000000^57 ≤ 4532008978977^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534098319 10000000000 4532008978977 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2351190047/5000000000 : ℝ), (6081186487/10000000000 : ℝ), (1534098319/10000000000 : ℝ)] ![(38048430105333/100000000000000 : ℝ), (26443775963391/50000000000000 : ℝ), (4532008978977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2351190047/5000000000 : ℝ)|^73 ≤ (38048430105333/100000000000000 : ℝ)^57
        have hw : |(2351190047/5000000000 : ℝ)|=(2351190047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6081186487/10000000000 : ℝ)|^73 ≤ (26443775963391/50000000000000 : ℝ)^57
        have hw : |(6081186487/10000000000 : ℝ)|=(6081186487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1534098319/10000000000 : ℝ)|^73 ≤ (4532008978977/50000000000000 : ℝ)^57
        have hw : |(1534098319/10000000000 : ℝ)|=(1534098319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-242178377/1250000000 : ℝ)*x 0 + (2818583751/10000000000 : ℝ)*x 1 + (-7401818419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242178377/1250000000 : ℝ)^73 ≤ (2444433644917/20000000000000 : ℝ)^57 := by
    have hnat : (242178377 : ℕ)^73*20000000000000^57 ≤ 2444433644917^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242178377 1250000000 2444433644917 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2818583751/10000000000 : ℝ)^73 ≤ (19753937029329/100000000000000 : ℝ)^57 := by
    have hnat : (2818583751 : ℕ)^73*100000000000000^57 ≤ 19753937029329^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818583751 10000000000 19753937029329 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7401818419/10000000000 : ℝ)^73 ≤ (68023894729207/100000000000000 : ℝ)^57 := by
    have hnat : (7401818419 : ℕ)^73*100000000000000^57 ≤ 68023894729207^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7401818419 10000000000 68023894729207 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242178377/1250000000 : ℝ), (2818583751/10000000000 : ℝ), (-7401818419/10000000000 : ℝ)] ![(2444433644917/20000000000000 : ℝ), (19753937029329/100000000000000 : ℝ), (68023894729207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242178377/1250000000 : ℝ)|^73 ≤ (2444433644917/20000000000000 : ℝ)^57
        have hw : |(-242178377/1250000000 : ℝ)|=(242178377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2818583751/10000000000 : ℝ)|^73 ≤ (19753937029329/100000000000000 : ℝ)^57
        have hw : |(2818583751/10000000000 : ℝ)|=(2818583751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7401818419/10000000000 : ℝ)|^73 ≤ (68023894729207/100000000000000 : ℝ)^57
        have hw : |(-7401818419/10000000000 : ℝ)|=(7401818419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1642140829/5000000000 : ℝ)*x 0 + (-1391953623/10000000000 : ℝ)*x 1 + (-924654797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1642140829/5000000000 : ℝ)^73 ≤ (24027266497331/100000000000000 : ℝ)^57 := by
    have hnat : (1642140829 : ℕ)^73*100000000000000^57 ≤ 24027266497331^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642140829 5000000000 24027266497331 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391953623/10000000000 : ℝ)^73 ≤ (2000685127461/25000000000000 : ℝ)^57 := by
    have hnat : (1391953623 : ℕ)^73*25000000000000^57 ≤ 2000685127461^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391953623 10000000000 2000685127461 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924654797/1250000000 : ℝ)^73 ≤ (67969992974497/100000000000000 : ℝ)^57 := by
    have hnat : (924654797 : ℕ)^73*100000000000000^57 ≤ 67969992974497^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924654797 1250000000 67969992974497 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1642140829/5000000000 : ℝ), (-1391953623/10000000000 : ℝ), (-924654797/1250000000 : ℝ)] ![(24027266497331/100000000000000 : ℝ), (2000685127461/25000000000000 : ℝ), (67969992974497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1642140829/5000000000 : ℝ)|^73 ≤ (24027266497331/100000000000000 : ℝ)^57
        have hw : |(1642140829/5000000000 : ℝ)|=(1642140829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1391953623/10000000000 : ℝ)|^73 ≤ (2000685127461/25000000000000 : ℝ)^57
        have hw : |(-1391953623/10000000000 : ℝ)|=(1391953623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924654797/1250000000 : ℝ)|^73 ≤ (67969992974497/100000000000000 : ℝ)^57
        have hw : |(-924654797/1250000000 : ℝ)|=(924654797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1757056867/5000000000 : ℝ)*x 0 + (7230648173/10000000000 : ℝ)*x 1 + (1361980759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757056867/5000000000 : ℝ)^73 ≤ (26201461416571/100000000000000 : ℝ)^57 := by
    have hnat : (1757056867 : ℕ)^73*100000000000000^57 ≤ 26201461416571^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757056867 5000000000 26201461416571 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7230648173/10000000000 : ℝ)^73 ≤ (66015821458869/100000000000000 : ℝ)^57 := by
    have hnat : (7230648173 : ℕ)^73*100000000000000^57 ≤ 66015821458869^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7230648173 10000000000 66015821458869 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361980759/10000000000 : ℝ)^73 ≤ (7782717116641/100000000000000 : ℝ)^57 := by
    have hnat : (1361980759 : ℕ)^73*100000000000000^57 ≤ 7782717116641^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361980759 10000000000 7782717116641 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1757056867/5000000000 : ℝ), (7230648173/10000000000 : ℝ), (1361980759/10000000000 : ℝ)] ![(26201461416571/100000000000000 : ℝ), (66015821458869/100000000000000 : ℝ), (7782717116641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1757056867/5000000000 : ℝ)|^73 ≤ (26201461416571/100000000000000 : ℝ)^57
        have hw : |(1757056867/5000000000 : ℝ)|=(1757056867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7230648173/10000000000 : ℝ)|^73 ≤ (66015821458869/100000000000000 : ℝ)^57
        have hw : |(7230648173/10000000000 : ℝ)|=(7230648173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361980759/10000000000 : ℝ)|^73 ≤ (7782717116641/100000000000000 : ℝ)^57
        have hw : |(1361980759/10000000000 : ℝ)|=(1361980759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2459800101/5000000000 : ℝ)*x 0 + (1336660509/2000000000 : ℝ)*x 1 + (-668251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2459800101/5000000000 : ℝ)^73 ≤ (40313821455967/100000000000000 : ℝ)^57 := by
    have hnat : (2459800101 : ℕ)^73*100000000000000^57 ≤ 40313821455967^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459800101 5000000000 40313821455967 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336660509/2000000000 : ℝ)^73 ≤ (11937017155041/20000000000000 : ℝ)^57 := by
    have hnat : (1336660509 : ℕ)^73*20000000000000^57 ≤ 11937017155041^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336660509 2000000000 11937017155041 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668251/5000000000 : ℝ)^73 ≤ (1092754207/100000000000000 : ℝ)^57 := by
    have hnat : (668251 : ℕ)^73*100000000000000^57 ≤ 1092754207^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668251 5000000000 1092754207 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2459800101/5000000000 : ℝ), (1336660509/2000000000 : ℝ), (-668251/5000000000 : ℝ)] ![(40313821455967/100000000000000 : ℝ), (11937017155041/20000000000000 : ℝ), (1092754207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2459800101/5000000000 : ℝ)|^73 ≤ (40313821455967/100000000000000 : ℝ)^57
        have hw : |(2459800101/5000000000 : ℝ)|=(2459800101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1336660509/2000000000 : ℝ)|^73 ≤ (11937017155041/20000000000000 : ℝ)^57
        have hw : |(1336660509/2000000000 : ℝ)|=(1336660509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668251/5000000000 : ℝ)|^73 ≤ (1092754207/100000000000000 : ℝ)^57
        have hw : |(-668251/5000000000 : ℝ)|=(668251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13276797/100000000 : ℝ)*x 0 + (3019106971/10000000000 : ℝ)*x 1 + (-1528945363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13276797/100000000 : ℝ)^73 ≤ (7532585503399/100000000000000 : ℝ)^57 := by
    have hnat : (13276797 : ℕ)^73*100000000000000^57 ≤ 7532585503399^57*100000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13276797 100000000 7532585503399 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3019106971/10000000000 : ℝ)^73 ≤ (674108037491/3125000000000 : ℝ)^57 := by
    have hnat : (3019106971 : ℕ)^73*3125000000000^57 ≤ 674108037491^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019106971 10000000000 674108037491 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528945363/2000000000 : ℝ)^73 ≤ (14179191454811/20000000000000 : ℝ)^57 := by
    have hnat : (1528945363 : ℕ)^73*20000000000000^57 ≤ 14179191454811^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528945363 2000000000 14179191454811 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13276797/100000000 : ℝ), (3019106971/10000000000 : ℝ), (-1528945363/2000000000 : ℝ)] ![(7532585503399/100000000000000 : ℝ), (674108037491/3125000000000 : ℝ), (14179191454811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13276797/100000000 : ℝ)|^73 ≤ (7532585503399/100000000000000 : ℝ)^57
        have hw : |(-13276797/100000000 : ℝ)|=(13276797/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3019106971/10000000000 : ℝ)|^73 ≤ (674108037491/3125000000000 : ℝ)^57
        have hw : |(3019106971/10000000000 : ℝ)|=(3019106971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1528945363/2000000000 : ℝ)|^73 ≤ (14179191454811/20000000000000 : ℝ)^57
        have hw : |(-1528945363/2000000000 : ℝ)|=(1528945363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2482229199/10000000000 : ℝ)*x 0 + (-391222239/2000000000 : ℝ)*x 1 + (-3819994029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2482229199/10000000000 : ℝ)^73 ≤ (8393496977649/50000000000000 : ℝ)^57 := by
    have hnat : (2482229199 : ℕ)^73*50000000000000^57 ≤ 8393496977649^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482229199 10000000000 8393496977649 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391222239/2000000000 : ℝ)^73 ≤ (12373326178711/100000000000000 : ℝ)^57 := by
    have hnat : (391222239 : ℕ)^73*100000000000000^57 ≤ 12373326178711^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391222239 2000000000 12373326178711 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3819994029/5000000000 : ℝ)^73 ≤ (442747999109/625000000000 : ℝ)^57 := by
    have hnat : (3819994029 : ℕ)^73*625000000000^57 ≤ 442747999109^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3819994029 5000000000 442747999109 625000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2482229199/10000000000 : ℝ), (-391222239/2000000000 : ℝ), (-3819994029/5000000000 : ℝ)] ![(8393496977649/50000000000000 : ℝ), (12373326178711/100000000000000 : ℝ), (442747999109/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2482229199/10000000000 : ℝ)|^73 ≤ (8393496977649/50000000000000 : ℝ)^57
        have hw : |(2482229199/10000000000 : ℝ)|=(2482229199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391222239/2000000000 : ℝ)|^73 ≤ (12373326178711/100000000000000 : ℝ)^57
        have hw : |(-391222239/2000000000 : ℝ)|=(391222239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3819994029/5000000000 : ℝ)|^73 ≤ (442747999109/625000000000 : ℝ)^57
        have hw : |(-3819994029/5000000000 : ℝ)|=(3819994029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6347824953/10000000000 : ℝ)*x 0 + (4500842583/10000000000 : ℝ)*x 1 + (706079747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6347824953/10000000000 : ℝ)^73 ≤ (13968874831413/25000000000000 : ℝ)^57 := by
    have hnat : (6347824953 : ℕ)^73*25000000000000^57 ≤ 13968874831413^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6347824953 10000000000 13968874831413 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500842583/10000000000 : ℝ)^73 ≤ (17986339893683/50000000000000 : ℝ)^57 := by
    have hnat : (4500842583 : ℕ)^73*50000000000000^57 ≤ 17986339893683^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500842583 10000000000 17986339893683 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706079747/5000000000 : ℝ)^73 ≤ (8151820861973/100000000000000 : ℝ)^57 := by
    have hnat : (706079747 : ℕ)^73*100000000000000^57 ≤ 8151820861973^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706079747 5000000000 8151820861973 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6347824953/10000000000 : ℝ), (4500842583/10000000000 : ℝ), (706079747/5000000000 : ℝ)] ![(13968874831413/25000000000000 : ℝ), (17986339893683/50000000000000 : ℝ), (8151820861973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6347824953/10000000000 : ℝ)|^73 ≤ (13968874831413/25000000000000 : ℝ)^57
        have hw : |(6347824953/10000000000 : ℝ)|=(6347824953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500842583/10000000000 : ℝ)|^73 ≤ (17986339893683/50000000000000 : ℝ)^57
        have hw : |(4500842583/10000000000 : ℝ)|=(4500842583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706079747/5000000000 : ℝ)|^73 ≤ (8151820861973/100000000000000 : ℝ)^57
        have hw : |(706079747/5000000000 : ℝ)|=(706079747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8323960471/10000000000 : ℝ)*x 0 + (184290981/625000000 : ℝ)*x 1 + (-7129059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8323960471/10000000000 : ℝ)^73 ≤ (79061764547231/100000000000000 : ℝ)^57 := by
    have hnat : (8323960471 : ℕ)^73*100000000000000^57 ≤ 79061764547231^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8323960471 10000000000 79061764547231 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184290981/625000000 : ℝ)^73 ≤ (20928909928141/100000000000000 : ℝ)^57 := by
    have hnat : (184290981 : ℕ)^73*100000000000000^57 ≤ 20928909928141^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184290981 625000000 20928909928141 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7129059/10000000000 : ℝ)^73 ≤ (9325515087/100000000000000 : ℝ)^57 := by
    have hnat : (7129059 : ℕ)^73*100000000000000^57 ≤ 9325515087^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7129059 10000000000 9325515087 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8323960471/10000000000 : ℝ), (184290981/625000000 : ℝ), (-7129059/10000000000 : ℝ)] ![(79061764547231/100000000000000 : ℝ), (20928909928141/100000000000000 : ℝ), (9325515087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8323960471/10000000000 : ℝ)|^73 ≤ (79061764547231/100000000000000 : ℝ)^57
        have hw : |(8323960471/10000000000 : ℝ)|=(8323960471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184290981/625000000 : ℝ)|^73 ≤ (20928909928141/100000000000000 : ℝ)^57
        have hw : |(184290981/625000000 : ℝ)|=(184290981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7129059/10000000000 : ℝ)|^73 ≤ (9325515087/100000000000000 : ℝ)^57
        have hw : |(-7129059/10000000000 : ℝ)|=(7129059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-100152379/1250000000 : ℝ)*x 0 + (1185765131/2000000000 : ℝ)*x 1 + (-5347533007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100152379/1250000000 : ℝ)^73 ≤ (493108313427/12500000000000 : ℝ)^57 := by
    have hnat : (100152379 : ℕ)^73*12500000000000^57 ≤ 493108313427^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100152379 1250000000 493108313427 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185765131/2000000000 : ℝ)^73 ≤ (25598268726333/50000000000000 : ℝ)^57 := by
    have hnat : (1185765131 : ℕ)^73*50000000000000^57 ≤ 25598268726333^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185765131 2000000000 25598268726333 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5347533007/10000000000 : ℝ)^73 ≤ (56073245041/125000000000 : ℝ)^57 := by
    have hnat : (5347533007 : ℕ)^73*125000000000^57 ≤ 56073245041^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347533007 10000000000 56073245041 125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100152379/1250000000 : ℝ), (1185765131/2000000000 : ℝ), (-5347533007/10000000000 : ℝ)] ![(493108313427/12500000000000 : ℝ), (25598268726333/50000000000000 : ℝ), (56073245041/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100152379/1250000000 : ℝ)|^73 ≤ (493108313427/12500000000000 : ℝ)^57
        have hw : |(-100152379/1250000000 : ℝ)|=(100152379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185765131/2000000000 : ℝ)|^73 ≤ (25598268726333/50000000000000 : ℝ)^57
        have hw : |(1185765131/2000000000 : ℝ)|=(1185765131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5347533007/10000000000 : ℝ)|^73 ≤ (56073245041/125000000000 : ℝ)^57
        have hw : |(-5347533007/10000000000 : ℝ)|=(5347533007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1548006929/2500000000 : ℝ)*x 0 + (-1056188293/10000000000 : ℝ)*x 1 + (-4914009461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1548006929/2500000000 : ℝ)^73 ≤ (13531315732547/25000000000000 : ℝ)^57 := by
    have hnat : (1548006929 : ℕ)^73*25000000000000^57 ≤ 13531315732547^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548006929 2500000000 13531315732547 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056188293/10000000000 : ℝ)^73 ≤ (2809789839697/50000000000000 : ℝ)^57 := by
    have hnat : (1056188293 : ℕ)^73*50000000000000^57 ≤ 2809789839697^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056188293 10000000000 2809789839697 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4914009461/10000000000 : ℝ)^73 ≤ (8051031475801/20000000000000 : ℝ)^57 := by
    have hnat : (4914009461 : ℕ)^73*20000000000000^57 ≤ 8051031475801^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914009461 10000000000 8051031475801 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1548006929/2500000000 : ℝ), (-1056188293/10000000000 : ℝ), (-4914009461/10000000000 : ℝ)] ![(13531315732547/25000000000000 : ℝ), (2809789839697/50000000000000 : ℝ), (8051031475801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1548006929/2500000000 : ℝ)|^73 ≤ (13531315732547/25000000000000 : ℝ)^57
        have hw : |(1548006929/2500000000 : ℝ)|=(1548006929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056188293/10000000000 : ℝ)|^73 ≤ (2809789839697/50000000000000 : ℝ)^57
        have hw : |(-1056188293/10000000000 : ℝ)|=(1056188293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4914009461/10000000000 : ℝ)|^73 ≤ (8051031475801/20000000000000 : ℝ)^57
        have hw : |(-4914009461/10000000000 : ℝ)|=(4914009461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3054585469/10000000000 : ℝ)*x 0 + (1464392617/2000000000 : ℝ)*x 1 + (1786695319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3054585469/10000000000 : ℝ)^73 ≤ (21896640252127/100000000000000 : ℝ)^57 := by
    have hnat : (3054585469 : ℕ)^73*100000000000000^57 ≤ 21896640252127^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3054585469 10000000000 21896640252127 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464392617/2000000000 : ℝ)^73 ≤ (13417087196079/20000000000000 : ℝ)^57 := by
    have hnat : (1464392617 : ℕ)^73*20000000000000^57 ≤ 13417087196079^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464392617 2000000000 13417087196079 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1786695319/10000000000 : ℝ)^73 ≤ (2203584750707/20000000000000 : ℝ)^57 := by
    have hnat : (1786695319 : ℕ)^73*20000000000000^57 ≤ 2203584750707^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786695319 10000000000 2203584750707 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3054585469/10000000000 : ℝ), (1464392617/2000000000 : ℝ), (1786695319/10000000000 : ℝ)] ![(21896640252127/100000000000000 : ℝ), (13417087196079/20000000000000 : ℝ), (2203584750707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3054585469/10000000000 : ℝ)|^73 ≤ (21896640252127/100000000000000 : ℝ)^57
        have hw : |(3054585469/10000000000 : ℝ)|=(3054585469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1464392617/2000000000 : ℝ)|^73 ≤ (13417087196079/20000000000000 : ℝ)^57
        have hw : |(1464392617/2000000000 : ℝ)|=(1464392617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1786695319/10000000000 : ℝ)|^73 ≤ (2203584750707/20000000000000 : ℝ)^57
        have hw : |(1786695319/10000000000 : ℝ)|=(1786695319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312060_s1_s1_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8856453599/10000000000 : ℝ)*x 0 + (2187210417/10000000000 : ℝ)*x 1 + (-55079749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8856453599/10000000000 : ℝ)^73 ≤ (42798209839883/50000000000000 : ℝ)^57 := by
    have hnat : (8856453599 : ℕ)^73*50000000000000^57 ≤ 42798209839883^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8856453599 10000000000 42798209839883 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187210417/10000000000 : ℝ)^73 ≤ (14275676218753/100000000000000 : ℝ)^57 := by
    have hnat : (2187210417 : ℕ)^73*100000000000000^57 ≤ 14275676218753^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187210417 10000000000 14275676218753 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55079749/10000000000 : ℝ)^73 ≤ (31976022369/25000000000000 : ℝ)^57 := by
    have hnat : (55079749 : ℕ)^73*25000000000000^57 ≤ 31976022369^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55079749 10000000000 31976022369 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8856453599/10000000000 : ℝ), (2187210417/10000000000 : ℝ), (-55079749/10000000000 : ℝ)] ![(42798209839883/50000000000000 : ℝ), (14275676218753/100000000000000 : ℝ), (31976022369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8856453599/10000000000 : ℝ)|^73 ≤ (42798209839883/50000000000000 : ℝ)^57
        have hw : |(8856453599/10000000000 : ℝ)|=(8856453599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2187210417/10000000000 : ℝ)|^73 ≤ (14275676218753/100000000000000 : ℝ)^57
        have hw : |(2187210417/10000000000 : ℝ)|=(2187210417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55079749/10000000000 : ℝ)|^73 ≤ (31976022369/25000000000000 : ℝ)^57
        have hw : |(-55079749/10000000000 : ℝ)|=(55079749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312060_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((85837/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85837/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5347/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5347/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-773/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-773/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33167/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33167/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1691/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1691/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-53863/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-53863/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (85837/100000 : ℝ) ^ (9/2 : ℝ) ≤ (50296224739394575809/100000000000000000000 : ℝ) := by
    have hpowers : (85837/100000 : ℝ)^9 ≤ (50296224739394575809/100000000000000000000 : ℝ)^2 := by
      have hnat : (85837 : ℕ)^9*100000000000000000000^2 ≤ 50296224739394575809^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85837 100000 50296224739394575809 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85837/100000 : ℝ)) (X := (50296224739394575809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (150296224739394575809/100000000000000000000 : ℝ) ≤ (10947672417526207/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (150296224739394575809/100000000000000000000 : ℝ)^2 ≤ (10947672417526207/10000000000000000 : ℝ)^9 := by
      have hnat : (150296224739394575809 : ℕ)^2*10000000000000000^9 ≤ 10947672417526207^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        150296224739394575809 100000000000000000000 10947672417526207 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10947672417526207/10000000000000000 : ℝ)) (X := (150296224739394575809/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (100296224739394575809/50000000000000000000 : ℝ) ≤ (5836480279926771/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (100296224739394575809/50000000000000000000 : ℝ)^2 ≤ (5836480279926771/5000000000000000 : ℝ)^9 := by
      have hnat : (100296224739394575809 : ℕ)^2*5000000000000000^9 ≤ 5836480279926771^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100296224739394575809 50000000000000000000 5836480279926771 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5836480279926771/5000000000000000 : ℝ)) (X := (100296224739394575809/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(947672417526207/8583700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(145057628465467/1716740000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (85837/100000 : ℝ)) (alpha := (947672417526207/8583700000000000 : ℝ)) (beta := (145057628465467/1716740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (85837/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(947672417526207/8583700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(145057628465467/1716740000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5347/6250 : ℝ) ^ (9/2 : ℝ) ≤ (12387274428086625653/25000000000000000000 : ℝ) := by
    have hpowers : (5347/6250 : ℝ)^9 ≤ (12387274428086625653/25000000000000000000 : ℝ)^2 := by
      have hnat : (5347 : ℕ)^9*25000000000000000000^2 ≤ 12387274428086625653^2*6250^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5347 6250 12387274428086625653 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5347/6250 : ℝ)) (X := (12387274428086625653/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (37387274428086625653/25000000000000000000 : ℝ) ≤ (5467777683895471/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (37387274428086625653/25000000000000000000 : ℝ)^2 ≤ (5467777683895471/5000000000000000 : ℝ)^9 := by
      have hnat : (37387274428086625653 : ℕ)^2*5000000000000000^9 ≤ 5467777683895471^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37387274428086625653 25000000000000000000 5467777683895471 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5467777683895471/5000000000000000 : ℝ)) (X := (37387274428086625653/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (24887274428086625653/12500000000000000000 : ℝ) ≤ (11653581164339007/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (24887274428086625653/12500000000000000000 : ℝ)^2 ≤ (11653581164339007/10000000000000000 : ℝ)^9 := by
      have hnat : (24887274428086625653 : ℕ)^2*10000000000000000^9 ≤ 11653581164339007^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24887274428086625653 12500000000000000000 11653581164339007 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11653581164339007/10000000000000000 : ℝ)) (X := (24887274428086625653/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(467777683895471/4277600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(143605159309613/1711040000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (5347/6250 : ℝ)) (alpha := (467777683895471/4277600000000000 : ℝ)) (beta := (143605159309613/1711040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5347/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(467777683895471/4277600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(143605159309613/1711040000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (773/1000 : ℝ) ^ (9/2 : ℝ) ≤ (15695592942529114037/50000000000000000000 : ℝ) := by
    have hpowers : (773/1000 : ℝ)^9 ≤ (15695592942529114037/50000000000000000000 : ℝ)^2 := by
      have hnat : (773 : ℕ)^9*50000000000000000000^2 ≤ 15695592942529114037^2*1000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        773 1000 15695592942529114037 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (773/1000 : ℝ)) (X := (15695592942529114037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (65695592942529114037/50000000000000000000 : ℝ) ≤ (5312733803710739/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (65695592942529114037/50000000000000000000 : ℝ)^2 ≤ (5312733803710739/5000000000000000 : ℝ)^9 := by
      have hnat : (65695592942529114037 : ℕ)^2*5000000000000000^9 ≤ 5312733803710739^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65695592942529114037 50000000000000000000 5312733803710739 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5312733803710739/5000000000000000 : ℝ)) (X := (65695592942529114037/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (40695592942529114037/25000000000000000000 : ℝ) ≤ (11143557553676687/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (40695592942529114037/25000000000000000000 : ℝ)^2 ≤ (11143557553676687/10000000000000000 : ℝ)^9 := by
      have hnat : (40695592942529114037 : ℕ)^2*10000000000000000^9 ≤ 11143557553676687^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40695592942529114037 25000000000000000000 11143557553676687 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11143557553676687/10000000000000000 : ℝ)) (X := (40695592942529114037/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(312733803710739/3865000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(518089946255209/7730000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (773/1000 : ℝ)) (alpha := (312733803710739/3865000000000000 : ℝ)) (beta := (518089946255209/7730000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (773/1000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(312733803710739/3865000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(518089946255209/7730000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-866124709/5000000000 : ℝ)*X 0 0+(2195963937/5000000000 : ℝ)*X 0 1+(-6229808503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4503263337/10000000000 : ℝ)*X 1 0+(-1836242641/10000000000 : ℝ)*X 1 1+(-1513654193/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2351190047/5000000000 : ℝ)*X 2 0+(6081186487/10000000000 : ℝ)*X 2 1+(1534098319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-242178377/1250000000 : ℝ)*X 0 0+(2818583751/10000000000 : ℝ)*X 0 1+(-7401818419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1642140829/5000000000 : ℝ)*X 1 0+(-1391953623/10000000000 : ℝ)*X 1 1+(-924654797/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1757056867/5000000000 : ℝ)*X 2 0+(7230648173/10000000000 : ℝ)*X 2 1+(1361980759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2459800101/5000000000 : ℝ)*X 0 0+(1336660509/2000000000 : ℝ)*X 0 1+(-668251/5000000000 : ℝ)*X 0 2+(2459800101/5000000000 : ℝ)*X 1 0+(1336660509/2000000000 : ℝ)*X 1 1+(-668251/5000000000 : ℝ)*X 1 2+(2459800101/5000000000 : ℝ)*X 2 0+(1336660509/2000000000 : ℝ)*X 2 1+(-668251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-13276797/100000000 : ℝ)*X 0 0+(3019106971/10000000000 : ℝ)*X 0 1+(-1528945363/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2482229199/10000000000 : ℝ)*X 1 0+(-391222239/2000000000 : ℝ)*X 1 1+(-3819994029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6347824953/10000000000 : ℝ)*X 2 0+(4500842583/10000000000 : ℝ)*X 2 1+(706079747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8323960471/10000000000 : ℝ)*X 0 0+(184290981/625000000 : ℝ)*X 0 1+(-7129059/10000000000 : ℝ)*X 0 2+(8323960471/10000000000 : ℝ)*X 1 0+(184290981/625000000 : ℝ)*X 1 1+(-7129059/10000000000 : ℝ)*X 1 2+(8323960471/10000000000 : ℝ)*X 2 0+(184290981/625000000 : ℝ)*X 2 1+(-7129059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-100152379/1250000000 : ℝ)*X 0 0+(1185765131/2000000000 : ℝ)*X 0 1+(-5347533007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1548006929/2500000000 : ℝ)*X 1 0+(-1056188293/10000000000 : ℝ)*X 1 1+(-4914009461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3054585469/10000000000 : ℝ)*X 2 0+(1464392617/2000000000 : ℝ)*X 2 1+(1786695319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8856453599/10000000000 : ℝ)*X 0 0+(2187210417/10000000000 : ℝ)*X 0 1+(-55079749/10000000000 : ℝ)*X 0 2+(8856453599/10000000000 : ℝ)*X 1 0+(2187210417/10000000000 : ℝ)*X 1 1+(-55079749/10000000000 : ℝ)*X 1 2+(8856453599/10000000000 : ℝ)*X 2 0+(2187210417/10000000000 : ℝ)*X 2 1+(-55079749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((33167/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33167/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (342167262936209222615376927/20666155000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37305214751/50000000000 : ℝ)*(base7) + (780887/500000000000 : ℝ)*(base59) + (1356663006887/500000000000 : ℝ)*(major_s1_0) + (1356663006887/500000000000 : ℝ)*(major_s1_1) + (1356663006887/500000000000 : ℝ)*(major_s1_2) + (4042639/200000000000 : ℝ)*(sp_s1_0) + (8279801/500000000000 : ℝ)*(sp_s1_1) + (3357551059493/1000000000000 : ℝ)*(sp_s1_7) + (26861049567/8000000000 : ℝ)*(sp_s1_8) + (3357664850779/1000000000000 : ℝ)*(sp_s1_9) + (2371697276857/1000000000000 : ℝ)*(sp_s1_13) + (94854653/1000000000000 : ℝ)*(sp_s1_14) + (2296483/125000000000 : ℝ)*(sp_s1_15) + (638281/500000000000 : ℝ)*(sp_s1_23) + (1625592981837/1000000000000 : ℝ)*(f.failure) + (3357666127341/1000000000000 : ℝ)*(f.sum) + (209107219461344191/41332310000000000000000000000000 : ℝ)*base62 + (683139279210883/3865000000000000000000000000 : ℝ)*base64 + (444543331779403/855520000000000000000000000 : ℝ)*base67 + (814666652891007/1932500000000000000000000000 : ℝ)*base68 + (64481499483862223129/331760005000000000000000000000000 : ℝ)*base71 + (435823855565819/858370000000000000000000000 : ℝ)*base73 + (861378203005863/2138800000000000000000000000 : ℝ)*base74 + (2667069160716761/4291850000000000000000000000 : ℝ)*base76 + (1674253522694612909/14687054048000000000000000000000 : ℝ)*base78 + (40819/100000000000000000 : ℝ)*base86 + (40819/100000000000000000 : ℝ)*base88 + (40819/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1691/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1691/2500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (91488182326252521/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (78806944801/100000000000 : ℝ)*(base7) + (2172863/500000000000 : ℝ)*(base18) + (115092080371/50000000000 : ℝ)*(major_s1_0) + (115092080371/50000000000 : ℝ)*(major_s1_1) + (115092080371/50000000000 : ℝ)*(major_s1_2) + (1489711/1000000000000 : ℝ)*(sp_s1_0) + (9141/12500000000 : ℝ)*(sp_s1_2) + (368597/500000000000 : ℝ)*(sp_s1_7) + (48562513/1000000000000 : ℝ)*(sp_s1_8) + (2756285203593/1000000000000 : ℝ)*(sp_s1_14) + (2756234522259/1000000000000 : ℝ)*(sp_s1_15) + (1378143349609/500000000000 : ℝ)*(sp_s1_16) + (2167109231687/1000000000000 : ℝ)*(sp_s1_20) + (26920187/1000000000000 : ℝ)*(sp_s1_27) + (172383337983/125000000000 : ℝ)*(f.failure) + (1378143715249/500000000000 : ℝ)*(f.sum) + (188137439532918597/4133231000000000000000000000000 : ℝ)*base63 + (138795649475839/386500000000000000000000000 : ℝ)*base64 + (6824940812027/17110400000000000000000000 : ℝ)*base67 + (1302758116929/3019531250000000000000000 : ℝ)*base68 + (3371993563532116607/33176000500000000000000000000000 : ℝ)*base71 + (65849600248773/214592500000000000000000000 : ℝ)*base73 + (80784922813891/213880000000000000000000000 : ℝ)*base74 + (353516647329051/858370000000000000000000000 : ℝ)*base76 + (2512738468512147417/36717635120000000000000000000000 : ℝ)*base78 + (6479/12500000000000000 : ℝ)*base87 + (6479/12500000000000000 : ℝ)*base89 + (6479/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-53863/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-53863/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1108951478476131327609/171674000000000000000000000 : ℝ) := by norm_num
    linear_combination (500501356901/1000000000000 : ℝ)*(base7) + (1404953/1000000000000 : ℝ)*(base34) + (25533378093/200000000000 : ℝ)*(base39) + (1068029/200000000000 : ℝ)*(base43) + (2336351166113/1000000000000 : ℝ)*(major_s1_0) + (58408680773/25000000000 : ℝ)*(major_s1_1) + (1168176285533/500000000000 : ℝ)*(major_s1_2) + (125701/31250000000 : ℝ)*(sp_s1_0) + (37479623/500000000000 : ℝ)*(sp_s1_9) + (3327951/500000000000 : ℝ)*(sp_s1_20) + (2975516557123/1000000000000 : ℝ)*(sp_s1_21) + (1487763662327/500000000000 : ℝ)*(sp_s1_22) + (2975447025263/1000000000000 : ℝ)*(sp_s1_23) + (1900236018941/1000000000000 : ℝ)*(sp_s1_27) + (279948544579/200000000000 : ℝ)*(f.failure) + (1487763662327/500000000000 : ℝ)*(f.sum) + (502682198004370543/5166538750000000000000000000000 : ℝ)*base62 + (1778042536044397/3865000000000000000000000000 : ℝ)*base64 + (25652136770363/213880000000000000000000000 : ℝ)*base66 + (568703156102637/1932500000000000000000000000 : ℝ)*base69 + (20356423502079034361/331760005000000000000000000000000 : ℝ)*base71 + (28481094048157/68669600000000000000000000 : ℝ)*base73 + (3292318841831/21388000000000000000000000 : ℝ)*base75 + (7626770441730349/8583700000000000000000000000 : ℝ)*base76 + (1053157664332501927/3671763512000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (5373/20000000000000000 : ℝ)*base86 + (14627/20000000000000000 : ℝ)*base89 + (5373/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((85837/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85837/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5347/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5347/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-773/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-773/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33167/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33167/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1691/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1691/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-53863/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-53863/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312060_s1 p hpa hpb X hX hprev0

#print axioms solution
