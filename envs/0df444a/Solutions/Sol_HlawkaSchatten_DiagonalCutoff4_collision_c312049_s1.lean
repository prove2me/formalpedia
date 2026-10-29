-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312049_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:18:00.399402+00:00
-- url     : https://prove2.me/submissions/8d6780e6-befe-4f61-bc3e-6131fb301a0f

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
theorem collision_support_c312049_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1413417391/5000000000 : ℝ)*x 0 + (-1413452097/5000000000 : ℝ)*x 1 + (3354717531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1413417391/5000000000 : ℝ)^37 ≤ (4987409582431/25000000000000 : ℝ)^29 := by
    have hnat : (1413417391 : ℕ)^37*25000000000000^29 ≤ 4987409582431^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413417391 5000000000 4987409582431 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413452097/5000000000 : ℝ)^37 ≤ (2493782915197/12500000000000 : ℝ)^29 := by
    have hnat : (1413452097 : ℕ)^37*12500000000000^29 ≤ 2493782915197^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413452097 5000000000 2493782915197 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3354717531/5000000000 : ℝ)^37 ≤ (60100098327933/100000000000000 : ℝ)^29 := by
    have hnat : (3354717531 : ℕ)^37*100000000000000^29 ≤ 60100098327933^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354717531 5000000000 60100098327933 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1413417391/5000000000 : ℝ), (-1413452097/5000000000 : ℝ), (3354717531/5000000000 : ℝ)] ![(4987409582431/25000000000000 : ℝ), (2493782915197/12500000000000 : ℝ), (60100098327933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1413417391/5000000000 : ℝ)|^37 ≤ (4987409582431/25000000000000 : ℝ)^29
        have hw : |(1413417391/5000000000 : ℝ)|=(1413417391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1413452097/5000000000 : ℝ)|^37 ≤ (2493782915197/12500000000000 : ℝ)^29
        have hw : |(-1413452097/5000000000 : ℝ)|=(1413452097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3354717531/5000000000 : ℝ)|^37 ≤ (60100098327933/100000000000000 : ℝ)^29
        have hw : |(3354717531/5000000000 : ℝ)|=(3354717531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2734286093/5000000000 : ℝ)*x 0 + (2734228771/5000000000 : ℝ)*x 1 + (-325006777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734286093/5000000000 : ℝ)^37 ≤ (361704027779/781250000000 : ℝ)^29 := by
    have hnat : (2734286093 : ℕ)^37*781250000000^29 ≤ 361704027779^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734286093 5000000000 361704027779 781250000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734228771/5000000000 : ℝ)^37 ≤ (11574219301601/25000000000000 : ℝ)^29 := by
    have hnat : (2734228771 : ℕ)^37*25000000000000^29 ≤ 11574219301601^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734228771 5000000000 11574219301601 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325006777/2500000000 : ℝ)^37 ≤ (3702503610787/50000000000000 : ℝ)^29 := by
    have hnat : (325006777 : ℕ)^37*50000000000000^29 ≤ 3702503610787^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325006777 2500000000 3702503610787 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734286093/5000000000 : ℝ), (2734228771/5000000000 : ℝ), (-325006777/2500000000 : ℝ)] ![(361704027779/781250000000 : ℝ), (11574219301601/25000000000000 : ℝ), (3702503610787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734286093/5000000000 : ℝ)|^37 ≤ (361704027779/781250000000 : ℝ)^29
        have hw : |(2734286093/5000000000 : ℝ)|=(2734286093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734228771/5000000000 : ℝ)|^37 ≤ (11574219301601/25000000000000 : ℝ)^29
        have hw : |(2734228771/5000000000 : ℝ)|=(2734228771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325006777/2500000000 : ℝ)|^37 ≤ (3702503610787/50000000000000 : ℝ)^29
        have hw : |(-325006777/2500000000 : ℝ)|=(325006777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1300956561/2500000000 : ℝ)*x 0 + (5203717149/10000000000 : ℝ)*x 1 + (253904283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300956561/2500000000 : ℝ)^37 ≤ (43457726675583/100000000000000 : ℝ)^29 := by
    have hnat : (1300956561 : ℕ)^37*100000000000000^29 ≤ 43457726675583^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300956561 2500000000 43457726675583 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203717149/10000000000 : ℝ)^37 ≤ (43456564286469/100000000000000 : ℝ)^29 := by
    have hnat : (5203717149 : ℕ)^37*100000000000000^29 ≤ 43456564286469^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203717149 10000000000 43456564286469 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253904283/1250000000 : ℝ)^37 ≤ (3271427256191/25000000000000 : ℝ)^29 := by
    have hnat : (253904283 : ℕ)^37*25000000000000^29 ≤ 3271427256191^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253904283 1250000000 3271427256191 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300956561/2500000000 : ℝ), (5203717149/10000000000 : ℝ), (253904283/1250000000 : ℝ)] ![(43457726675583/100000000000000 : ℝ), (43456564286469/100000000000000 : ℝ), (3271427256191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300956561/2500000000 : ℝ)|^37 ≤ (43457726675583/100000000000000 : ℝ)^29
        have hw : |(1300956561/2500000000 : ℝ)|=(1300956561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203717149/10000000000 : ℝ)|^37 ≤ (43456564286469/100000000000000 : ℝ)^29
        have hw : |(5203717149/10000000000 : ℝ)|=(5203717149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253904283/1250000000 : ℝ)|^37 ≤ (3271427256191/25000000000000 : ℝ)^29
        have hw : |(253904283/1250000000 : ℝ)|=(253904283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3384958633/10000000000 : ℝ)*x 0 + (1487117833/5000000000 : ℝ)*x 1 + (766802941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3384958633/10000000000 : ℝ)^37 ≤ (12552926560821/50000000000000 : ℝ)^29 := by
    have hnat : (3384958633 : ℕ)^37*50000000000000^29 ≤ 12552926560821^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3384958633 10000000000 12552926560821 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1487117833/5000000000 : ℝ)^37 ≤ (5321568145511/25000000000000 : ℝ)^29 := by
    have hnat : (1487117833 : ℕ)^37*25000000000000^29 ≤ 5321568145511^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487117833 5000000000 5321568145511 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766802941/1250000000 : ℝ)^37 ≤ (53607874274313/100000000000000 : ℝ)^29 := by
    have hnat : (766802941 : ℕ)^37*100000000000000^29 ≤ 53607874274313^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766802941 1250000000 53607874274313 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3384958633/10000000000 : ℝ), (1487117833/5000000000 : ℝ), (766802941/1250000000 : ℝ)] ![(12552926560821/50000000000000 : ℝ), (5321568145511/25000000000000 : ℝ), (53607874274313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3384958633/10000000000 : ℝ)|^37 ≤ (12552926560821/50000000000000 : ℝ)^29
        have hw : |(-3384958633/10000000000 : ℝ)|=(3384958633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1487117833/5000000000 : ℝ)|^37 ≤ (5321568145511/25000000000000 : ℝ)^29
        have hw : |(1487117833/5000000000 : ℝ)|=(1487117833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766802941/1250000000 : ℝ)|^37 ≤ (53607874274313/100000000000000 : ℝ)^29
        have hw : |(766802941/1250000000 : ℝ)|=(766802941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2600049773/10000000000 : ℝ)*x 0 + (-571141453/2500000000 : ℝ)*x 1 + (1458920439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600049773/10000000000 : ℝ)^37 ≤ (8965350995677/50000000000000 : ℝ)^29 := by
    have hnat : (2600049773 : ℕ)^37*50000000000000^29 ≤ 8965350995677^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600049773 10000000000 8965350995677 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571141453/2500000000 : ℝ)^37 ≤ (3800685524513/25000000000000 : ℝ)^29 := by
    have hnat : (571141453 : ℕ)^37*25000000000000^29 ≤ 3800685524513^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571141453 2500000000 3800685524513 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458920439/2000000000 : ℝ)^37 ≤ (1044789935849/1562500000000 : ℝ)^29 := by
    have hnat : (1458920439 : ℕ)^37*1562500000000^29 ≤ 1044789935849^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458920439 2000000000 1044789935849 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600049773/10000000000 : ℝ), (-571141453/2500000000 : ℝ), (1458920439/2000000000 : ℝ)] ![(8965350995677/50000000000000 : ℝ), (3800685524513/25000000000000 : ℝ), (1044789935849/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600049773/10000000000 : ℝ)|^37 ≤ (8965350995677/50000000000000 : ℝ)^29
        have hw : |(2600049773/10000000000 : ℝ)|=(2600049773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571141453/2500000000 : ℝ)|^37 ≤ (3800685524513/25000000000000 : ℝ)^29
        have hw : |(-571141453/2500000000 : ℝ)|=(571141453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458920439/2000000000 : ℝ)|^37 ≤ (1044789935849/1562500000000 : ℝ)^29
        have hw : |(1458920439/2000000000 : ℝ)|=(1458920439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1262288021/2500000000 : ℝ)*x 0 + (317062237/500000000 : ℝ)*x 1 + (-256329739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1262288021/2500000000 : ℝ)^37 ≤ (8363300006627/20000000000000 : ℝ)^29 := by
    have hnat : (1262288021 : ℕ)^37*20000000000000^29 ≤ 8363300006627^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262288021 2500000000 8363300006627 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317062237/500000000 : ℝ)^37 ≤ (55924481662691/100000000000000 : ℝ)^29 := by
    have hnat : (317062237 : ℕ)^37*100000000000000^29 ≤ 55924481662691^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317062237 500000000 55924481662691 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256329739/5000000000 : ℝ)^37 ≤ (564754572421/25000000000000 : ℝ)^29 := by
    have hnat : (256329739 : ℕ)^37*25000000000000^29 ≤ 564754572421^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256329739 5000000000 564754572421 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1262288021/2500000000 : ℝ), (317062237/500000000 : ℝ), (-256329739/5000000000 : ℝ)] ![(8363300006627/20000000000000 : ℝ), (55924481662691/100000000000000 : ℝ), (564754572421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1262288021/2500000000 : ℝ)|^37 ≤ (8363300006627/20000000000000 : ℝ)^29
        have hw : |(1262288021/2500000000 : ℝ)|=(1262288021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(317062237/500000000 : ℝ)|^37 ≤ (55924481662691/100000000000000 : ℝ)^29
        have hw : |(317062237/500000000 : ℝ)|=(317062237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256329739/5000000000 : ℝ)|^37 ≤ (564754572421/25000000000000 : ℝ)^29
        have hw : |(-256329739/5000000000 : ℝ)|=(256329739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4983407417/10000000000 : ℝ)*x 0 + (6258675823/10000000000 : ℝ)*x 1 + (78331509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4983407417/10000000000 : ℝ)^37 ≤ (514038221777/1250000000000 : ℝ)^29 := by
    have hnat : (4983407417 : ℕ)^37*1250000000000^29 ≤ 514038221777^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983407417 10000000000 514038221777 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6258675823/10000000000 : ℝ)^37 ≤ (10999417393643/20000000000000 : ℝ)^29 := by
    have hnat : (6258675823 : ℕ)^37*20000000000000^29 ≤ 10999417393643^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6258675823 10000000000 10999417393643 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78331509/1000000000 : ℝ)^37 ≤ (484981908869/12500000000000 : ℝ)^29 := by
    have hnat : (78331509 : ℕ)^37*12500000000000^29 ≤ 484981908869^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78331509 1000000000 484981908869 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4983407417/10000000000 : ℝ), (6258675823/10000000000 : ℝ), (78331509/1000000000 : ℝ)] ![(514038221777/1250000000000 : ℝ), (10999417393643/20000000000000 : ℝ), (484981908869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4983407417/10000000000 : ℝ)|^37 ≤ (514038221777/1250000000000 : ℝ)^29
        have hw : |(4983407417/10000000000 : ℝ)|=(4983407417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6258675823/10000000000 : ℝ)|^37 ≤ (10999417393643/20000000000000 : ℝ)^29
        have hw : |(6258675823/10000000000 : ℝ)|=(6258675823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78331509/1000000000 : ℝ)|^37 ≤ (484981908869/12500000000000 : ℝ)^29
        have hw : |(78331509/1000000000 : ℝ)|=(78331509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-743536299/2500000000 : ℝ)*x 0 + (338504623/1000000000 : ℝ)*x 1 + (245376931/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (743536299/2500000000 : ℝ)^37 ≤ (21285446485631/100000000000000 : ℝ)^29 := by
    have hnat : (743536299 : ℕ)^37*100000000000000^29 ≤ 21285446485631^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743536299 2500000000 21285446485631 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338504623/1000000000 : ℝ)^37 ≤ (25106682048339/100000000000000 : ℝ)^29 := by
    have hnat : (338504623 : ℕ)^37*100000000000000^29 ≤ 25106682048339^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338504623 1000000000 25106682048339 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245376931/400000000 : ℝ)^37 ≤ (53607871453469/100000000000000 : ℝ)^29 := by
    have hnat : (245376931 : ℕ)^37*100000000000000^29 ≤ 53607871453469^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245376931 400000000 53607871453469 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-743536299/2500000000 : ℝ), (338504623/1000000000 : ℝ), (245376931/400000000 : ℝ)] ![(21285446485631/100000000000000 : ℝ), (25106682048339/100000000000000 : ℝ), (53607871453469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-743536299/2500000000 : ℝ)|^37 ≤ (21285446485631/100000000000000 : ℝ)^29
        have hw : |(-743536299/2500000000 : ℝ)|=(743536299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338504623/1000000000 : ℝ)|^37 ≤ (25106682048339/100000000000000 : ℝ)^29
        have hw : |(338504623/1000000000 : ℝ)|=(338504623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(245376931/400000000 : ℝ)|^37 ≤ (53607871453469/100000000000000 : ℝ)^29
        have hw : |(245376931/400000000 : ℝ)|=(245376931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1142248109/5000000000 : ℝ)*x 0 + (-130005847/500000000 : ℝ)*x 1 + (1458920437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142248109/5000000000 : ℝ)^37 ≤ (118766806469/781250000000 : ℝ)^29 := by
    have hnat : (1142248109 : ℕ)^37*781250000000^29 ≤ 118766806469^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142248109 5000000000 118766806469 781250000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130005847/500000000 : ℝ)^37 ≤ (8965646488447/50000000000000 : ℝ)^29 := by
    have hnat : (130005847 : ℕ)^37*50000000000000^29 ≤ 8965646488447^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130005847 500000000 8965646488447 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458920437/2000000000 : ℝ)^37 ≤ (66866555777383/100000000000000 : ℝ)^29 := by
    have hnat : (1458920437 : ℕ)^37*100000000000000^29 ≤ 66866555777383^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458920437 2000000000 66866555777383 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1142248109/5000000000 : ℝ), (-130005847/500000000 : ℝ), (1458920437/2000000000 : ℝ)] ![(118766806469/781250000000 : ℝ), (8965646488447/50000000000000 : ℝ), (66866555777383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1142248109/5000000000 : ℝ)|^37 ≤ (118766806469/781250000000 : ℝ)^29
        have hw : |(1142248109/5000000000 : ℝ)|=(1142248109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130005847/500000000 : ℝ)|^37 ≤ (8965646488447/50000000000000 : ℝ)^29
        have hw : |(-130005847/500000000 : ℝ)|=(130005847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458920437/2000000000 : ℝ)|^37 ≤ (66866555777383/100000000000000 : ℝ)^29
        have hw : |(1458920437/2000000000 : ℝ)|=(1458920437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3170678671/5000000000 : ℝ)*x 0 + (5049032073/10000000000 : ℝ)*x 1 + (-64082459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3170678671/5000000000 : ℝ)^37 ≤ (1747679645867/3125000000000 : ℝ)^29 := by
    have hnat : (3170678671 : ℕ)^37*3125000000000^29 ≤ 1747679645867^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170678671 5000000000 1747679645867 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5049032073/10000000000 : ℝ)^37 ≤ (41815231935813/100000000000000 : ℝ)^29 := by
    have hnat : (5049032073 : ℕ)^37*100000000000000^29 ≤ 41815231935813^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049032073 10000000000 41815231935813 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64082459/1250000000 : ℝ)^37 ≤ (2259019380361/100000000000000 : ℝ)^29 := by
    have hnat : (64082459 : ℕ)^37*100000000000000^29 ≤ 2259019380361^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64082459 1250000000 2259019380361 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3170678671/5000000000 : ℝ), (5049032073/10000000000 : ℝ), (-64082459/1250000000 : ℝ)] ![(1747679645867/3125000000000 : ℝ), (41815231935813/100000000000000 : ℝ), (2259019380361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3170678671/5000000000 : ℝ)|^37 ≤ (1747679645867/3125000000000 : ℝ)^29
        have hw : |(3170678671/5000000000 : ℝ)|=(3170678671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5049032073/10000000000 : ℝ)|^37 ≤ (41815231935813/100000000000000 : ℝ)^29
        have hw : |(5049032073/10000000000 : ℝ)|=(5049032073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64082459/1250000000 : ℝ)|^37 ≤ (2259019380361/100000000000000 : ℝ)^29
        have hw : |(-64082459/1250000000 : ℝ)|=(64082459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_18 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6258786899/10000000000 : ℝ)*x 0 + (4983288921/10000000000 : ℝ)*x 1 + (156663089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6258786899/10000000000 : ℝ)^37 ≤ (54998332291907/100000000000000 : ℝ)^29 := by
    have hnat : (6258786899 : ℕ)^37*100000000000000^29 ≤ 54998332291907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6258786899 10000000000 54998332291907 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4983288921/10000000000 : ℝ)^37 ≤ (20560905085973/50000000000000 : ℝ)^29 := by
    have hnat : (4983288921 : ℕ)^37*50000000000000^29 ≤ 20560905085973^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983288921 10000000000 20560905085973 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156663089/2000000000 : ℝ)^37 ≤ (6207772023/160000000000 : ℝ)^29 := by
    have hnat : (156663089 : ℕ)^37*160000000000^29 ≤ 6207772023^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156663089 2000000000 6207772023 160000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6258786899/10000000000 : ℝ), (4983288921/10000000000 : ℝ), (156663089/2000000000 : ℝ)] ![(54998332291907/100000000000000 : ℝ), (20560905085973/50000000000000 : ℝ), (6207772023/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6258786899/10000000000 : ℝ)|^37 ≤ (54998332291907/100000000000000 : ℝ)^29
        have hw : |(6258786899/10000000000 : ℝ)|=(6258786899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4983288921/10000000000 : ℝ)|^37 ≤ (20560905085973/50000000000000 : ℝ)^29
        have hw : |(4983288921/10000000000 : ℝ)|=(4983288921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156663089/2000000000 : ℝ)|^37 ≤ (6207772023/160000000000 : ℝ)^29
        have hw : |(156663089/2000000000 : ℝ)|=(156663089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194657001/5000000000 : ℝ)*x 0 + (1881904109/5000000000 : ℝ)*x 1 + (903470631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194657001/5000000000 : ℝ)^37 ≤ (34974172727303/100000000000000 : ℝ)^29 := by
    have hnat : (2194657001 : ℕ)^37*100000000000000^29 ≤ 34974172727303^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194657001 5000000000 34974172727303 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881904109/5000000000 : ℝ)^37 ≤ (7186198597303/25000000000000 : ℝ)^29 := by
    have hnat : (1881904109 : ℕ)^37*25000000000000^29 ≤ 7186198597303^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881904109 5000000000 7186198597303 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903470631/2000000000 : ℝ)^37 ≤ (1133782276957/3125000000000 : ℝ)^29 := by
    have hnat : (903470631 : ℕ)^37*3125000000000^29 ≤ 1133782276957^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903470631 2000000000 1133782276957 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194657001/5000000000 : ℝ), (1881904109/5000000000 : ℝ), (903470631/2000000000 : ℝ)] ![(34974172727303/100000000000000 : ℝ), (7186198597303/25000000000000 : ℝ), (1133782276957/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194657001/5000000000 : ℝ)|^37 ≤ (34974172727303/100000000000000 : ℝ)^29
        have hw : |(-2194657001/5000000000 : ℝ)|=(2194657001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1881904109/5000000000 : ℝ)|^37 ≤ (7186198597303/25000000000000 : ℝ)^29
        have hw : |(1881904109/5000000000 : ℝ)|=(1881904109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903470631/2000000000 : ℝ)|^37 ≤ (1133782276957/3125000000000 : ℝ)^29
        have hw : |(903470631/2000000000 : ℝ)|=(903470631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2151333057/10000000000 : ℝ)*x 0 + (-111080111/400000000 : ℝ)*x 1 + (3628074713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151333057/10000000000 : ℝ)^37 ≤ (14080789382241/100000000000000 : ℝ)^29 := by
    have hnat : (2151333057 : ℕ)^37*100000000000000^29 ≤ 14080789382241^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151333057 10000000000 14080789382241 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111080111/400000000 : ℝ)^37 ≤ (19502043661831/100000000000000 : ℝ)^29 := by
    have hnat : (111080111 : ℕ)^37*100000000000000^29 ≤ 19502043661831^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111080111 400000000 19502043661831 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3628074713/5000000000 : ℝ)^37 ≤ (33208583467821/50000000000000 : ℝ)^29 := by
    have hnat : (3628074713 : ℕ)^37*50000000000000^29 ≤ 33208583467821^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628074713 5000000000 33208583467821 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151333057/10000000000 : ℝ), (-111080111/400000000 : ℝ), (3628074713/5000000000 : ℝ)] ![(14080789382241/100000000000000 : ℝ), (19502043661831/100000000000000 : ℝ), (33208583467821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151333057/10000000000 : ℝ)|^37 ≤ (14080789382241/100000000000000 : ℝ)^29
        have hw : |(2151333057/10000000000 : ℝ)|=(2151333057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111080111/400000000 : ℝ)|^37 ≤ (19502043661831/100000000000000 : ℝ)^29
        have hw : |(-111080111/400000000 : ℝ)|=(111080111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3628074713/5000000000 : ℝ)|^37 ≤ (33208583467821/50000000000000 : ℝ)^29
        have hw : |(3628074713/5000000000 : ℝ)|=(3628074713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1092693803/2000000000 : ℝ)*x 0 + (5418537231/10000000000 : ℝ)*x 1 + (-690514683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092693803/2000000000 : ℝ)^37 ≤ (9248599921171/20000000000000 : ℝ)^29 := by
    have hnat : (1092693803 : ℕ)^37*20000000000000^29 ≤ 9248599921171^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092693803 2000000000 9248599921171 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418537231/10000000000 : ℝ)^37 ≤ (1143958383589/2500000000000 : ℝ)^29 := by
    have hnat : (5418537231 : ℕ)^37*2500000000000^29 ≤ 1143958383589^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418537231 10000000000 1143958383589 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690514683/5000000000 : ℝ)^37 ≤ (124979141261/1562500000000 : ℝ)^29 := by
    have hnat : (690514683 : ℕ)^37*1562500000000^29 ≤ 124979141261^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690514683 5000000000 124979141261 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092693803/2000000000 : ℝ), (5418537231/10000000000 : ℝ), (-690514683/5000000000 : ℝ)] ![(9248599921171/20000000000000 : ℝ), (1143958383589/2500000000000 : ℝ), (124979141261/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092693803/2000000000 : ℝ)|^37 ≤ (9248599921171/20000000000000 : ℝ)^29
        have hw : |(1092693803/2000000000 : ℝ)|=(1092693803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418537231/10000000000 : ℝ)|^37 ≤ (1143958383589/2500000000000 : ℝ)^29
        have hw : |(5418537231/10000000000 : ℝ)|=(5418537231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-690514683/5000000000 : ℝ)|^37 ≤ (124979141261/1562500000000 : ℝ)^29
        have hw : |(-690514683/5000000000 : ℝ)|=(690514683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312049_s1_s1_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4159942837/10000000000 : ℝ)*x 0 + (5418537231/10000000000 : ℝ)*x 1 + (1503302099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4159942837/10000000000 : ℝ)^37 ≤ (16329692963889/50000000000000 : ℝ)^29 := by
    have hnat : (4159942837 : ℕ)^37*50000000000000^29 ≤ 16329692963889^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159942837 10000000000 16329692963889 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418537231/10000000000 : ℝ)^37 ≤ (1143958383589/2500000000000 : ℝ)^29 := by
    have hnat : (5418537231 : ℕ)^37*2500000000000^29 ≤ 1143958383589^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418537231 10000000000 1143958383589 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503302099/5000000000 : ℝ)^37 ≤ (10791139354401/50000000000000 : ℝ)^29 := by
    have hnat : (1503302099 : ℕ)^37*50000000000000^29 ≤ 10791139354401^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503302099 5000000000 10791139354401 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4159942837/10000000000 : ℝ), (5418537231/10000000000 : ℝ), (1503302099/5000000000 : ℝ)] ![(16329692963889/50000000000000 : ℝ), (1143958383589/2500000000000 : ℝ), (10791139354401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4159942837/10000000000 : ℝ)|^37 ≤ (16329692963889/50000000000000 : ℝ)^29
        have hw : |(4159942837/10000000000 : ℝ)|=(4159942837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418537231/10000000000 : ℝ)|^37 ≤ (1143958383589/2500000000000 : ℝ)^29
        have hw : |(5418537231/10000000000 : ℝ)|=(5418537231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503302099/5000000000 : ℝ)|^37 ≤ (10791139354401/50000000000000 : ℝ)^29
        have hw : |(1503302099/5000000000 : ℝ)|=(1503302099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312049_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15633/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15633/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19543/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19543/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9477/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(9477/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(591/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(591/12500 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  have s1_pow0 : (15633/20000 : ℝ) ^ (9/2 : ℝ) ≤ (8250789432475211321/25000000000000000000 : ℝ) := by
    have hpowers : (15633/20000 : ℝ)^9 ≤ (8250789432475211321/25000000000000000000 : ℝ)^2 := by
      have hnat : (15633 : ℕ)^9*25000000000000000000^2 ≤ 8250789432475211321^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15633 20000 8250789432475211321 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15633/20000 : ℝ)) (X := (8250789432475211321/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (33250789432475211321/25000000000000000000 : ℝ) ≤ (2130859788495963/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (33250789432475211321/25000000000000000000 : ℝ)^2 ≤ (2130859788495963/2000000000000000 : ℝ)^9 := by
      have hnat : (33250789432475211321 : ℕ)^2*2000000000000000^9 ≤ 2130859788495963^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33250789432475211321 25000000000000000000 2130859788495963 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2130859788495963/2000000000000000 : ℝ)) (X := (33250789432475211321/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (20750789432475211321/12500000000000000000 : ℝ) ≤ (5596114404453147/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (20750789432475211321/12500000000000000000 : ℝ)^2 ≤ (5596114404453147/5000000000000000 : ℝ)^9 := by
      have hnat : (20750789432475211321 : ℕ)^2*5000000000000000^9 ≤ 5596114404453147^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20750789432475211321 12500000000000000000 5596114404453147 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5596114404453147/5000000000000000 : ℝ)) (X := (20750789432475211321/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(130859788495963/1563300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(179309955475493/2605500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (15633/20000 : ℝ)) (alpha := (130859788495963/1563300000000000 : ℝ)) (beta := (179309955475493/2605500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15633/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(130859788495963/1563300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(179309955475493/2605500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (19543/25000 : ℝ) ^ (9/2 : ℝ) ≤ (33016459878003318837/100000000000000000000 : ℝ) := by
    have hpowers : (19543/25000 : ℝ)^9 ≤ (33016459878003318837/100000000000000000000 : ℝ)^2 := by
      have hnat : (19543 : ℕ)^9*100000000000000000000^2 ≤ 33016459878003318837^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19543 25000 33016459878003318837 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19543/25000 : ℝ)) (X := (33016459878003318837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (133016459878003318837/100000000000000000000 : ℝ) ≤ (17047257164939/16000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (133016459878003318837/100000000000000000000 : ℝ)^2 ≤ (17047257164939/16000000000000 : ℝ)^9 := by
      have hnat : (133016459878003318837 : ℕ)^2*16000000000000^9 ≤ 17047257164939^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133016459878003318837 100000000000000000000 17047257164939 16000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (17047257164939/16000000000000 : ℝ)) (X := (133016459878003318837/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (83016459878003318837/50000000000000000000 : ℝ) ≤ (5596313689250633/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (83016459878003318837/50000000000000000000 : ℝ)^2 ≤ (5596313689250633/5000000000000000 : ℝ)^9 := by
      have hnat : (83016459878003318837 : ℕ)^2*5000000000000000^9 ≤ 5596313689250633^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83016459878003318837 50000000000000000000 5596313689250633 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5596313689250633/5000000000000000 : ℝ)) (X := (83016459878003318837/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1047257164939/12507520000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(538091650414391/7817200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (19543/25000 : ℝ)) (alpha := (1047257164939/12507520000000 : ℝ)) (beta := (538091650414391/7817200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (19543/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1047257164939/12507520000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(538091650414391/7817200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9477/50000 : ℝ) ^ (9/2 : ℝ) ≤ (56189341604034911/100000000000000000000 : ℝ) := by
    have hpowers : (9477/50000 : ℝ)^9 ≤ (56189341604034911/100000000000000000000 : ℝ)^2 := by
      have hnat : (9477 : ℕ)^9*100000000000000000000^2 ≤ 56189341604034911^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9477 50000 56189341604034911 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9477/50000 : ℝ)) (X := (56189341604034911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100056189341604034911/100000000000000000000 : ℝ) ≤ (5000624189639189/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (100056189341604034911/100000000000000000000 : ℝ)^2 ≤ (5000624189639189/5000000000000000 : ℝ)^9 := by
      have hnat : (100056189341604034911 : ℕ)^2*5000000000000000^9 ≤ 5000624189639189^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056189341604034911 100000000000000000000 5000624189639189 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000624189639189/5000000000000000 : ℝ)) (X := (100056189341604034911/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50056189341604034911/50000000000000000000 : ℝ) ≤ (25006240533513/25000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50056189341604034911/50000000000000000000 : ℝ)^2 ≤ (25006240533513/25000000000000 : ℝ)^9 := by
      have hnat : (50056189341604034911 : ℕ)^2*25000000000000^9 ≤ 25006240533513^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056189341604034911 50000000000000000000 25006240533513 25000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25006240533513/25000000000000 : ℝ)) (X := (50056189341604034911/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(208063213063/315900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(623917063411/947700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (9477/50000 : ℝ)) (alpha := (208063213063/315900000000000 : ℝ)) (beta := (623917063411/947700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (9477/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(208063213063/315900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(623917063411/947700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1413417391/5000000000 : ℝ)*X 1 0+(-1413452097/5000000000 : ℝ)*X 1 1+(3354717531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2734286093/5000000000 : ℝ)*X 2 0+(2734228771/5000000000 : ℝ)*X 2 1+(-325006777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1300956561/2500000000 : ℝ)*X 0 0+(5203717149/10000000000 : ℝ)*X 0 1+(253904283/1250000000 : ℝ)*X 0 2+(1300956561/2500000000 : ℝ)*X 1 0+(5203717149/10000000000 : ℝ)*X 1 1+(253904283/1250000000 : ℝ)*X 1 2+(1300956561/2500000000 : ℝ)*X 2 0+(5203717149/10000000000 : ℝ)*X 2 1+(253904283/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3384958633/10000000000 : ℝ)*X 0 0+(1487117833/5000000000 : ℝ)*X 0 1+(766802941/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2600049773/10000000000 : ℝ)*X 1 0+(-571141453/2500000000 : ℝ)*X 1 1+(1458920439/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1262288021/2500000000 : ℝ)*X 2 0+(317062237/500000000 : ℝ)*X 2 1+(-256329739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4983407417/10000000000 : ℝ)*X 0 0+(6258675823/10000000000 : ℝ)*X 0 1+(78331509/1000000000 : ℝ)*X 0 2+(4983407417/10000000000 : ℝ)*X 1 0+(6258675823/10000000000 : ℝ)*X 1 1+(78331509/1000000000 : ℝ)*X 1 2+(4983407417/10000000000 : ℝ)*X 2 0+(6258675823/10000000000 : ℝ)*X 2 1+(78331509/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-743536299/2500000000 : ℝ)*X 0 0+(338504623/1000000000 : ℝ)*X 0 1+(245376931/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1142248109/5000000000 : ℝ)*X 1 0+(-130005847/500000000 : ℝ)*X 1 1+(1458920437/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3170678671/5000000000 : ℝ)*X 2 0+(5049032073/10000000000 : ℝ)*X 2 1+(-64082459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((6258786899/10000000000 : ℝ)*X 0 0+(4983288921/10000000000 : ℝ)*X 0 1+(156663089/2000000000 : ℝ)*X 0 2+(6258786899/10000000000 : ℝ)*X 1 0+(4983288921/10000000000 : ℝ)*X 1 1+(156663089/2000000000 : ℝ)*X 1 2+(6258786899/10000000000 : ℝ)*X 2 0+(4983288921/10000000000 : ℝ)*X 2 1+(156663089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-2194657001/5000000000 : ℝ)*X 0 0+(1881904109/5000000000 : ℝ)*X 0 1+(903470631/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2151333057/10000000000 : ℝ)*X 1 0+(-111080111/400000000 : ℝ)*X 1 1+(3628074713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1092693803/2000000000 : ℝ)*X 2 0+(5418537231/10000000000 : ℝ)*X 2 1+(-690514683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((4159942837/10000000000 : ℝ)*X 0 0+(5418537231/10000000000 : ℝ)*X 0 1+(1503302099/5000000000 : ℝ)*X 0 2+(4159942837/10000000000 : ℝ)*X 1 0+(5418537231/10000000000 : ℝ)*X 1 1+(1503302099/5000000000 : ℝ)*X 1 2+(4159942837/10000000000 : ℝ)*X 2 0+(5418537231/10000000000 : ℝ)*X 2 1+(1503302099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312049_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((21671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (268203847598533942589627/25403625000000000000000000000 : ℝ) := by norm_num
    linear_combination (2331523/1000000000000 : ℝ)*(base39) + (1731165577/12500000000 : ℝ)*(base49) + (649272226659/250000000000 : ℝ)*(base59) + (1440484205457/1000000000000 : ℝ)*(base60) + (1392030654351/250000000000 : ℝ)*(major_s1_0) + (1392030654351/250000000000 : ℝ)*(major_s1_1) + (1392030654351/250000000000 : ℝ)*(major_s1_2) + (59522561/1000000000000 : ℝ)*(sp_s1_1) + (7800199613931/1000000000000 : ℝ)*(sp_s1_7) + (3900119573193/500000000000 : ℝ)*(sp_s1_8) + (3900149334473/500000000000 : ℝ)*(sp_s1_9) + (667181040833/200000000000 : ℝ)*(sp_s1_12) + (19811003/200000000000 : ℝ)*(sp_s1_13) + (18921227/500000000000 : ℝ)*(sp_s1_25) + (3335943046619/1000000000000 : ℝ)*(f.failure) + (3900149334473/500000000000 : ℝ)*(f.sum) + (230181529207771787/2057877900000000000000000000000 : ℝ)*base62 + (123272350229651/157950000000000000000000000 : ℝ)*base65 + (1642305657802709/1954300000000000000000000000 : ℝ)*base67 + (10321322826263/52650000000000000000000000 : ℝ)*base69 + (14335461699931127/30484350000000000000000000000 : ℝ)*base71 + (23023119514511/54281250000000000000000000 : ℝ)*base72 + (281339380890663/390860000000000000000000000 : ℝ)*base75 + (204581582645347/260550000000000000000000000 : ℝ)*base77 + (4230653867603691653/16973095500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (82853/100000000000000000 : ℝ)*base86 + (82853/100000000000000000 : ℝ)*base88 + (82853/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43343/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64070265261606372967919083/4654341031640625000000000000000 : ℝ) := by norm_num
    linear_combination (15034731/1000000000000 : ℝ)*(base21) + (771821/200000000000 : ℝ)*(base39) + (69247637697/500000000000 : ℝ)*(base49) + (63069422299/25000000000 : ℝ)*(base59) + (847292412637/500000000000 : ℝ)*(base60) + (556812294977/100000000000 : ℝ)*(major_s1_0) + (556812294977/100000000000 : ℝ)*(major_s1_1) + (556812294977/100000000000 : ℝ)*(major_s1_2) + (57114261/1000000000000 : ℝ)*(sp_s1_6) + (185409699/1000000000000 : ℝ)*(sp_s1_8) + (975037258153/125000000000 : ℝ)*(sp_s1_13) + (312004506221/40000000000 : ℝ)*(sp_s1_14) + (7800283030493/1000000000000 : ℝ)*(sp_s1_15) + (3335886131483/1000000000000 : ℝ)*(sp_s1_18) + (667188649149/200000000000 : ℝ)*(f.failure) + (975037258153/125000000000 : ℝ)*(f.sum) + (1700727373328949397/2469453480000000000000000000000 : ℝ)*base63 + (19479238666249/94770000000000000000000000 : ℝ)*base65 + (7973896752897/156344000000000000000000000 : ℝ)*base67 + (22063402292647/31590000000000000000000000 : ℝ)*base69 + (513623743689089/2286326250000000000000000000 : ℝ)*base71 + (5265694357433/130275000000000000000000000 : ℝ)*base73 + (200628987901671/781720000000000000000000000 : ℝ)*base75 + (46232304313729/78165000000000000000000000 : ℝ)*base77 + (312019343508572527/20367714600000000000000000000000 : ℝ)*base79 + (7037/20000000000000000 : ℝ)*base87 + (7037/20000000000000000 : ℝ)*base89 + (7037/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(591/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(591/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50630899860370890503166297287/3971704347000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7923401239/10000000000 : ℝ)*(base5) + (2377381/1000000000000 : ℝ)*(base40) + (73508479491/200000000000 : ℝ)*(base49) + (649607445991/1000000000000 : ℝ)*(base59) + (1493958422519/1000000000000 : ℝ)*(major_s1_0) + (1493958422519/1000000000000 : ℝ)*(major_s1_1) + (1493958422519/1000000000000 : ℝ)*(major_s1_2) + (42074853/1000000000000 : ℝ)*(sp_s1_1) + (43865399/62500000000 : ℝ)*(sp_s1_2) + (3026023/250000000000 : ℝ)*(sp_s1_9) + (2092860429321/1000000000000 : ℝ)*(sp_s1_19) + (523204588617/250000000000 : ℝ)*(sp_s1_20) + (576897320549/200000000000 : ℝ)*(sp_s1_21) + (10271204251/100000000000 : ℝ)*(sp_s1_25) + (895052166409/1000000000000 : ℝ)*(f.failure) + (2092860429321/1000000000000 : ℝ)*(f.sum) + (4527450129327162449/24694534800000000000000000000000 : ℝ)*base62 + (217150676238931/947700000000000000000000000 : ℝ)*base65 + (2120938730715129/7817200000000000000000000000 : ℝ)*base66 + (21608310606977/315900000000000000000000000 : ℝ)*base68 + (15217862311561367/45726525000000000000000000000 : ℝ)*base70 + (1100377464458167/2605500000000000000000000000 : ℝ)*base73 + (246280295132143/1563440000000000000000000000 : ℝ)*base74 + (1031980554564493/1563300000000000000000000000 : ℝ)*base76 + (21451988152594806829/203677146000000000000000000000000 : ℝ)*base79 + (74583/100000000000000000 : ℝ)*base86 + (74583/100000000000000000 : ℝ)*base88 + (74583/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15633/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15633/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19543/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19543/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(9477/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(9477/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(591/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(591/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312049_s1 p hpa hpb X hX hprev0

#print axioms solution
