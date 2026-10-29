-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312053_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:18:45.281174+00:00
-- url     : https://prove2.me/submissions/6e6db8fb-0131-4f89-8101-1e54de53a573

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
theorem collision_support_c312053_s3_s3_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2556492533/10000000000 : ℝ)*x 0 + (2503712099/5000000000 : ℝ)*x 1 + (2508048261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2556492533/10000000000 : ℝ)^73 ≤ (17432886737449/100000000000000 : ℝ)^57 := by
    have hnat : (2556492533 : ℕ)^73*100000000000000^57 ≤ 17432886737449^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556492533 10000000000 17432886737449 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503712099/5000000000 : ℝ)^73 ≤ (41237811983757/100000000000000 : ℝ)^57 := by
    have hnat : (2503712099 : ℕ)^73*100000000000000^57 ≤ 41237811983757^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503712099 5000000000 41237811983757 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508048261/5000000000 : ℝ)^73 ≤ (10332325317441/25000000000000 : ℝ)^57 := by
    have hnat : (2508048261 : ℕ)^73*25000000000000^57 ≤ 10332325317441^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508048261 5000000000 10332325317441 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2556492533/10000000000 : ℝ), (2503712099/5000000000 : ℝ), (2508048261/5000000000 : ℝ)] ![(17432886737449/100000000000000 : ℝ), (41237811983757/100000000000000 : ℝ), (10332325317441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2556492533/10000000000 : ℝ)|^73 ≤ (17432886737449/100000000000000 : ℝ)^57
        have hw : |(-2556492533/10000000000 : ℝ)|=(2556492533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2503712099/5000000000 : ℝ)|^73 ≤ (41237811983757/100000000000000 : ℝ)^57
        have hw : |(2503712099/5000000000 : ℝ)|=(2503712099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508048261/5000000000 : ℝ)|^73 ≤ (10332325317441/25000000000000 : ℝ)^57
        have hw : |(2508048261/5000000000 : ℝ)|=(2508048261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4479832797/10000000000 : ℝ)*x 0 + (-129375131/625000000 : ℝ)*x 1 + (5905510543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479832797/10000000000 : ℝ)^73 ≤ (35757766305997/100000000000000 : ℝ)^57 := by
    have hnat : (4479832797 : ℕ)^73*100000000000000^57 ≤ 35757766305997^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479832797 10000000000 35757766305997 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129375131/625000000 : ℝ)^73 ≤ (13303398013013/100000000000000 : ℝ)^57 := by
    have hnat : (129375131 : ℕ)^73*100000000000000^57 ≤ 13303398013013^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129375131 625000000 13303398013013 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5905510543/10000000000 : ℝ)^73 ≤ (50938835667097/100000000000000 : ℝ)^57 := by
    have hnat : (5905510543 : ℕ)^73*100000000000000^57 ≤ 50938835667097^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5905510543 10000000000 50938835667097 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479832797/10000000000 : ℝ), (-129375131/625000000 : ℝ), (5905510543/10000000000 : ℝ)] ![(35757766305997/100000000000000 : ℝ), (13303398013013/100000000000000 : ℝ), (50938835667097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479832797/10000000000 : ℝ)|^73 ≤ (35757766305997/100000000000000 : ℝ)^57
        have hw : |(4479832797/10000000000 : ℝ)|=(4479832797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129375131/625000000 : ℝ)|^73 ≤ (13303398013013/100000000000000 : ℝ)^57
        have hw : |(-129375131/625000000 : ℝ)|=(129375131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5905510543/10000000000 : ℝ)|^73 ≤ (50938835667097/100000000000000 : ℝ)^57
        have hw : |(5905510543/10000000000 : ℝ)|=(5905510543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2246036023/5000000000 : ℝ)*x 0 + (5900128963/10000000000 : ℝ)*x 1 + (-2062012903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246036023/5000000000 : ℝ)^73 ≤ (17941464909011/50000000000000 : ℝ)^57 := by
    have hnat : (2246036023 : ℕ)^73*50000000000000^57 ≤ 17941464909011^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246036023 5000000000 17941464909011 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5900128963/10000000000 : ℝ)^73 ≤ (50879393613053/100000000000000 : ℝ)^57 := by
    have hnat : (5900128963 : ℕ)^73*100000000000000^57 ≤ 50879393613053^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5900128963 10000000000 50879393613053 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062012903/10000000000 : ℝ)^73 ≤ (1654709569487/12500000000000 : ℝ)^57 := by
    have hnat : (2062012903 : ℕ)^73*12500000000000^57 ≤ 1654709569487^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062012903 10000000000 1654709569487 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246036023/5000000000 : ℝ), (5900128963/10000000000 : ℝ), (-2062012903/10000000000 : ℝ)] ![(17941464909011/50000000000000 : ℝ), (50879393613053/100000000000000 : ℝ), (1654709569487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246036023/5000000000 : ℝ)|^73 ≤ (17941464909011/50000000000000 : ℝ)^57
        have hw : |(2246036023/5000000000 : ℝ)|=(2246036023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5900128963/10000000000 : ℝ)|^73 ≤ (50879393613053/100000000000000 : ℝ)^57
        have hw : |(5900128963/10000000000 : ℝ)|=(5900128963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062012903/10000000000 : ℝ)|^73 ≤ (1654709569487/12500000000000 : ℝ)^57
        have hw : |(-2062012903/10000000000 : ℝ)|=(2062012903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1284526247/2000000000 : ℝ)*x 0 + (3033672913/10000000000 : ℝ)*x 1 + (1509745679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284526247/2000000000 : ℝ)^73 ≤ (56720191073099/100000000000000 : ℝ)^57 := by
    have hnat : (1284526247 : ℕ)^73*100000000000000^57 ≤ 56720191073099^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284526247 2000000000 56720191073099 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3033672913/10000000000 : ℝ)^73 ≤ (21704834278301/100000000000000 : ℝ)^57 := by
    have hnat : (3033672913 : ℕ)^73*100000000000000^57 ≤ 21704834278301^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033672913 10000000000 21704834278301 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1509745679/5000000000 : ℝ)^73 ≤ (2696871828689/12500000000000 : ℝ)^57 := by
    have hnat : (1509745679 : ℕ)^73*12500000000000^57 ≤ 2696871828689^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509745679 5000000000 2696871828689 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1284526247/2000000000 : ℝ), (3033672913/10000000000 : ℝ), (1509745679/5000000000 : ℝ)] ![(56720191073099/100000000000000 : ℝ), (21704834278301/100000000000000 : ℝ), (2696871828689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1284526247/2000000000 : ℝ)|^73 ≤ (56720191073099/100000000000000 : ℝ)^57
        have hw : |(1284526247/2000000000 : ℝ)|=(1284526247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3033672913/10000000000 : ℝ)|^73 ≤ (21704834278301/100000000000000 : ℝ)^57
        have hw : |(3033672913/10000000000 : ℝ)|=(3033672913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1509745679/5000000000 : ℝ)|^73 ≤ (2696871828689/12500000000000 : ℝ)^57
        have hw : |(1509745679/5000000000 : ℝ)|=(1509745679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-319178829/1250000000 : ℝ)*x 0 + (2428113209/5000000000 : ℝ)*x 1 + (323029031/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319178829/1250000000 : ℝ)^73 ≤ (3481230215633/20000000000000 : ℝ)^57 := by
    have hnat : (319178829 : ℕ)^73*20000000000000^57 ≤ 3481230215633^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319178829 1250000000 3481230215633 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2428113209/5000000000 : ℝ)^73 ≤ (39649935549537/100000000000000 : ℝ)^57 := by
    have hnat : (2428113209 : ℕ)^73*100000000000000^57 ≤ 39649935549537^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428113209 5000000000 39649935549537 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323029031/625000000 : ℝ)^73 ≤ (42943913358557/100000000000000 : ℝ)^57 := by
    have hnat : (323029031 : ℕ)^73*100000000000000^57 ≤ 42943913358557^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323029031 625000000 42943913358557 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319178829/1250000000 : ℝ), (2428113209/5000000000 : ℝ), (323029031/625000000 : ℝ)] ![(3481230215633/20000000000000 : ℝ), (39649935549537/100000000000000 : ℝ), (42943913358557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319178829/1250000000 : ℝ)|^73 ≤ (3481230215633/20000000000000 : ℝ)^57
        have hw : |(-319178829/1250000000 : ℝ)|=(319178829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2428113209/5000000000 : ℝ)|^73 ≤ (39649935549537/100000000000000 : ℝ)^57
        have hw : |(2428113209/5000000000 : ℝ)|=(2428113209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323029031/625000000 : ℝ)|^73 ≤ (42943913358557/100000000000000 : ℝ)^57
        have hw : |(323029031/625000000 : ℝ)|=(323029031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4449460969/10000000000 : ℝ)*x 0 + (-401368049/2000000000 : ℝ)*x 1 + (5980313767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449460969/10000000000 : ℝ)^73 ≤ (35447586588567/100000000000000 : ℝ)^57 := by
    have hnat : (4449460969 : ℕ)^73*100000000000000^57 ≤ 35447586588567^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449460969 10000000000 35447586588567 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401368049/2000000000 : ℝ)^73 ≤ (639288549727/5000000000000 : ℝ)^57 := by
    have hnat : (401368049 : ℕ)^73*5000000000000^57 ≤ 639288549727^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401368049 2000000000 639288549727 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5980313767/10000000000 : ℝ)^73 ≤ (10353328479049/20000000000000 : ℝ)^57 := by
    have hnat : (5980313767 : ℕ)^73*20000000000000^57 ≤ 10353328479049^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5980313767 10000000000 10353328479049 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449460969/10000000000 : ℝ), (-401368049/2000000000 : ℝ), (5980313767/10000000000 : ℝ)] ![(35447586588567/100000000000000 : ℝ), (639288549727/5000000000000 : ℝ), (10353328479049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449460969/10000000000 : ℝ)|^73 ≤ (35447586588567/100000000000000 : ℝ)^57
        have hw : |(4449460969/10000000000 : ℝ)|=(4449460969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401368049/2000000000 : ℝ)|^73 ≤ (639288549727/5000000000000 : ℝ)^57
        have hw : |(-401368049/2000000000 : ℝ)|=(401368049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5980313767/10000000000 : ℝ)|^73 ≤ (10353328479049/20000000000000 : ℝ)^57
        have hw : |(5980313767/10000000000 : ℝ)|=(5980313767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4461701761/10000000000 : ℝ)*x 0 + (241573023/400000000 : ℝ)*x 1 + (-1910584333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4461701761/10000000000 : ℝ)^73 ≤ (4446565925583/12500000000000 : ℝ)^57 := by
    have hnat : (4461701761 : ℕ)^73*12500000000000^57 ≤ 4446565925583^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461701761 10000000000 4446565925583 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241573023/400000000 : ℝ)^73 ≤ (26210874962639/50000000000000 : ℝ)^57 := by
    have hnat : (241573023 : ℕ)^73*50000000000000^57 ≤ 26210874962639^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241573023 400000000 26210874962639 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910584333/10000000000 : ℝ)^73 ≤ (12005722664241/100000000000000 : ℝ)^57 := by
    have hnat : (1910584333 : ℕ)^73*100000000000000^57 ≤ 12005722664241^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910584333 10000000000 12005722664241 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4461701761/10000000000 : ℝ), (241573023/400000000 : ℝ), (-1910584333/10000000000 : ℝ)] ![(4446565925583/12500000000000 : ℝ), (26210874962639/50000000000000 : ℝ), (12005722664241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4461701761/10000000000 : ℝ)|^73 ≤ (4446565925583/12500000000000 : ℝ)^57
        have hw : |(4461701761/10000000000 : ℝ)|=(4461701761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241573023/400000000 : ℝ)|^73 ≤ (26210874962639/50000000000000 : ℝ)^57
        have hw : |(241573023/400000000 : ℝ)|=(241573023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910584333/10000000000 : ℝ)|^73 ≤ (12005722664241/100000000000000 : ℝ)^57
        have hw : |(-1910584333/10000000000 : ℝ)|=(1910584333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (100229347/156250000 : ℝ)*x 0 + (803363083/2500000000 : ℝ)*x 1 + (2846414809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100229347/156250000 : ℝ)^73 ≤ (28315127941943/50000000000000 : ℝ)^57 := by
    have hnat : (100229347 : ℕ)^73*50000000000000^57 ≤ 28315127941943^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100229347 156250000 28315127941943 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803363083/2500000000 : ℝ)^73 ≤ (4673131417399/20000000000000 : ℝ)^57 := by
    have hnat : (803363083 : ℕ)^73*20000000000000^57 ≤ 4673131417399^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803363083 2500000000 4673131417399 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2846414809/10000000000 : ℝ)^73 ≤ (5001021752281/25000000000000 : ℝ)^57 := by
    have hnat : (2846414809 : ℕ)^73*25000000000000^57 ≤ 5001021752281^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846414809 10000000000 5001021752281 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100229347/156250000 : ℝ), (803363083/2500000000 : ℝ), (2846414809/10000000000 : ℝ)] ![(28315127941943/50000000000000 : ℝ), (4673131417399/20000000000000 : ℝ), (5001021752281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100229347/156250000 : ℝ)|^73 ≤ (28315127941943/50000000000000 : ℝ)^57
        have hw : |(100229347/156250000 : ℝ)|=(100229347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803363083/2500000000 : ℝ)|^73 ≤ (4673131417399/20000000000000 : ℝ)^57
        have hw : |(803363083/2500000000 : ℝ)|=(803363083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2846414809/10000000000 : ℝ)|^73 ≤ (5001021752281/25000000000000 : ℝ)^57
        have hw : |(2846414809/10000000000 : ℝ)|=(2846414809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1205243033/5000000000 : ℝ)*x 0 + (1247725889/2500000000 : ℝ)*x 1 + (2575972279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1205243033/5000000000 : ℝ)^73 ≤ (16168149254341/100000000000000 : ℝ)^57 := by
    have hnat : (1205243033 : ℕ)^73*100000000000000^57 ≤ 16168149254341^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205243033 5000000000 16168149254341 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247725889/2500000000 : ℝ)^73 ≤ (410636494039/1000000000000 : ℝ)^57 := by
    have hnat : (1247725889 : ℕ)^73*1000000000000^57 ≤ 410636494039^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247725889 2500000000 410636494039 1000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575972279/5000000000 : ℝ)^73 ≤ (8553640267091/20000000000000 : ℝ)^57 := by
    have hnat : (2575972279 : ℕ)^73*20000000000000^57 ≤ 8553640267091^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575972279 5000000000 8553640267091 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1205243033/5000000000 : ℝ), (1247725889/2500000000 : ℝ), (2575972279/5000000000 : ℝ)] ![(16168149254341/100000000000000 : ℝ), (410636494039/1000000000000 : ℝ), (8553640267091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1205243033/5000000000 : ℝ)|^73 ≤ (16168149254341/100000000000000 : ℝ)^57
        have hw : |(-1205243033/5000000000 : ℝ)|=(1205243033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1247725889/2500000000 : ℝ)|^73 ≤ (410636494039/1000000000000 : ℝ)^57
        have hw : |(1247725889/2500000000 : ℝ)|=(1247725889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575972279/5000000000 : ℝ)|^73 ≤ (8553640267091/20000000000000 : ℝ)^57
        have hw : |(2575972279/5000000000 : ℝ)|=(2575972279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (881493317/2000000000 : ℝ)*x 0 + (-408717881/2000000000 : ℝ)*x 1 + (18724349/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881493317/2000000000 : ℝ)^73 ≤ (35019687349023/100000000000000 : ℝ)^57 := by
    have hnat : (881493317 : ℕ)^73*100000000000000^57 ≤ 35019687349023^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881493317 2000000000 35019687349023 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408717881/2000000000 : ℝ)^73 ≤ (6543196039939/50000000000000 : ℝ)^57 := by
    have hnat : (408717881 : ℕ)^73*50000000000000^57 ≤ 6543196039939^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408717881 2000000000 6543196039939 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18724349/31250000 : ℝ)^73 ≤ (51893920552089/100000000000000 : ℝ)^57 := by
    have hnat : (18724349 : ℕ)^73*100000000000000^57 ≤ 51893920552089^57*31250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18724349 31250000 51893920552089 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(881493317/2000000000 : ℝ), (-408717881/2000000000 : ℝ), (18724349/31250000 : ℝ)] ![(35019687349023/100000000000000 : ℝ), (6543196039939/50000000000000 : ℝ), (51893920552089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(881493317/2000000000 : ℝ)|^73 ≤ (35019687349023/100000000000000 : ℝ)^57
        have hw : |(881493317/2000000000 : ℝ)|=(881493317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408717881/2000000000 : ℝ)|^73 ≤ (6543196039939/50000000000000 : ℝ)^57
        have hw : |(-408717881/2000000000 : ℝ)|=(408717881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18724349/31250000 : ℝ)|^73 ≤ (51893920552089/100000000000000 : ℝ)^57
        have hw : |(18724349/31250000 : ℝ)|=(18724349/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4639014173/10000000000 : ℝ)*x 0 + (586285709/1000000000 : ℝ)*x 1 + (-1927104243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4639014173/10000000000 : ℝ)^73 ≤ (37393042915243/100000000000000 : ℝ)^57 := by
    have hnat : (4639014173 : ℕ)^73*100000000000000^57 ≤ 37393042915243^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639014173 10000000000 37393042915243 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586285709/1000000000 : ℝ)^73 ≤ (5046812663837/10000000000000 : ℝ)^57 := by
    have hnat : (586285709 : ℕ)^73*10000000000000^57 ≤ 5046812663837^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586285709 1000000000 5046812663837 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1927104243/10000000000 : ℝ)^73 ≤ (12138830433753/100000000000000 : ℝ)^57 := by
    have hnat : (1927104243 : ℕ)^73*100000000000000^57 ≤ 12138830433753^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927104243 10000000000 12138830433753 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4639014173/10000000000 : ℝ), (586285709/1000000000 : ℝ), (-1927104243/10000000000 : ℝ)] ![(37393042915243/100000000000000 : ℝ), (5046812663837/10000000000000 : ℝ), (12138830433753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4639014173/10000000000 : ℝ)|^73 ≤ (37393042915243/100000000000000 : ℝ)^57
        have hw : |(4639014173/10000000000 : ℝ)|=(4639014173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586285709/1000000000 : ℝ)|^73 ≤ (5046812663837/10000000000000 : ℝ)^57
        have hw : |(586285709/1000000000 : ℝ)|=(586285709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1927104243/10000000000 : ℝ)|^73 ≤ (12138830433753/100000000000000 : ℝ)^57
        have hw : |(-1927104243/10000000000 : ℝ)|=(1927104243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1318646581/2000000000 : ℝ)*x 0 + (755017327/2500000000 : ℝ)*x 1 + (2819576417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318646581/2000000000 : ℝ)^73 ≤ (29328444522137/50000000000000 : ℝ)^57 := by
    have hnat : (1318646581 : ℕ)^73*50000000000000^57 ≤ 29328444522137^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318646581 2000000000 29328444522137 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755017327/2500000000 : ℝ)^73 ≤ (4316052708547/20000000000000 : ℝ)^57 := by
    have hnat : (755017327 : ℕ)^73*20000000000000^57 ≤ 4316052708547^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755017327 2500000000 4316052708547 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819576417/10000000000 : ℝ)^73 ≤ (197628473911/1000000000000 : ℝ)^57 := by
    have hnat : (2819576417 : ℕ)^73*1000000000000^57 ≤ 197628473911^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819576417 10000000000 197628473911 1000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318646581/2000000000 : ℝ), (755017327/2500000000 : ℝ), (2819576417/10000000000 : ℝ)] ![(29328444522137/50000000000000 : ℝ), (4316052708547/20000000000000 : ℝ), (197628473911/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318646581/2000000000 : ℝ)|^73 ≤ (29328444522137/50000000000000 : ℝ)^57
        have hw : |(1318646581/2000000000 : ℝ)|=(1318646581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(755017327/2500000000 : ℝ)|^73 ≤ (4316052708547/20000000000000 : ℝ)^57
        have hw : |(755017327/2500000000 : ℝ)|=(755017327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819576417/10000000000 : ℝ)|^73 ≤ (197628473911/1000000000000 : ℝ)^57
        have hw : |(2819576417/10000000000 : ℝ)|=(2819576417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1198205093/5000000000 : ℝ)*x 0 + (1014596127/2000000000 : ℝ)*x 1 + (508163759/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1198205093/5000000000 : ℝ)^73 ≤ (3209466750411/20000000000000 : ℝ)^57 := by
    have hnat : (1198205093 : ℕ)^73*20000000000000^57 ≤ 3209466750411^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198205093 5000000000 3209466750411 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014596127/2000000000 : ℝ)^73 ≤ (41930502678191/100000000000000 : ℝ)^57 := by
    have hnat : (1014596127 : ℕ)^73*100000000000000^57 ≤ 41930502678191^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014596127 2000000000 41930502678191 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508163759/1000000000 : ℝ)^73 ≤ (42022163551391/100000000000000 : ℝ)^57 := by
    have hnat : (508163759 : ℕ)^73*100000000000000^57 ≤ 42022163551391^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508163759 1000000000 42022163551391 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1198205093/5000000000 : ℝ), (1014596127/2000000000 : ℝ), (508163759/1000000000 : ℝ)] ![(3209466750411/20000000000000 : ℝ), (41930502678191/100000000000000 : ℝ), (42022163551391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1198205093/5000000000 : ℝ)|^73 ≤ (3209466750411/20000000000000 : ℝ)^57
        have hw : |(-1198205093/5000000000 : ℝ)|=(1198205093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014596127/2000000000 : ℝ)|^73 ≤ (41930502678191/100000000000000 : ℝ)^57
        have hw : |(1014596127/2000000000 : ℝ)|=(1014596127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508163759/1000000000 : ℝ)|^73 ≤ (42022163551391/100000000000000 : ℝ)^57
        have hw : |(508163759/1000000000 : ℝ)|=(508163759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (464084919/1000000000 : ℝ)*x 0 + (-389406829/2000000000 : ℝ)*x 1 + (182703983/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464084919/1000000000 : ℝ)^73 ≤ (18705993580369/50000000000000 : ℝ)^57 := by
    have hnat : (464084919 : ℕ)^73*50000000000000^57 ≤ 18705993580369^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464084919 1000000000 18705993580369 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389406829/2000000000 : ℝ)^73 ≤ (1229984055219/10000000000000 : ℝ)^57 := by
    have hnat : (389406829 : ℕ)^73*10000000000000^57 ≤ 1229984055219^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389406829 2000000000 1229984055219 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182703983/312500000 : ℝ)^73 ≤ (12572043065551/25000000000000 : ℝ)^57 := by
    have hnat : (182703983 : ℕ)^73*25000000000000^57 ≤ 12572043065551^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182703983 312500000 12572043065551 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(464084919/1000000000 : ℝ), (-389406829/2000000000 : ℝ), (182703983/312500000 : ℝ)] ![(18705993580369/50000000000000 : ℝ), (1229984055219/10000000000000 : ℝ), (12572043065551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(464084919/1000000000 : ℝ)|^73 ≤ (18705993580369/50000000000000 : ℝ)^57
        have hw : |(464084919/1000000000 : ℝ)|=(464084919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389406829/2000000000 : ℝ)|^73 ≤ (1229984055219/10000000000000 : ℝ)^57
        have hw : |(-389406829/2000000000 : ℝ)|=(389406829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182703983/312500000 : ℝ)|^73 ≤ (12572043065551/25000000000000 : ℝ)^57
        have hw : |(182703983/312500000 : ℝ)|=(182703983/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (137899949/312500000 : ℝ)*x 0 + (6012871837/10000000000 : ℝ)*x 1 + (-2008362369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137899949/312500000 : ℝ)^73 ≤ (4384244006263/12500000000000 : ℝ)^57 := by
    have hnat : (137899949 : ℕ)^73*12500000000000^57 ≤ 4384244006263^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137899949 312500000 4384244006263 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6012871837/10000000000 : ℝ)^73 ≤ (26063927946017/50000000000000 : ℝ)^57 := by
    have hnat : (6012871837 : ℕ)^73*50000000000000^57 ≤ 26063927946017^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012871837 10000000000 26063927946017 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008362369/10000000000 : ℝ)^73 ≤ (12798192046497/100000000000000 : ℝ)^57 := by
    have hnat : (2008362369 : ℕ)^73*100000000000000^57 ≤ 12798192046497^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008362369 10000000000 12798192046497 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(137899949/312500000 : ℝ), (6012871837/10000000000 : ℝ), (-2008362369/10000000000 : ℝ)] ![(4384244006263/12500000000000 : ℝ), (26063927946017/50000000000000 : ℝ), (12798192046497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(137899949/312500000 : ℝ)|^73 ≤ (4384244006263/12500000000000 : ℝ)^57
        have hw : |(137899949/312500000 : ℝ)|=(137899949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6012871837/10000000000 : ℝ)|^73 ≤ (26063927946017/50000000000000 : ℝ)^57
        have hw : |(6012871837/10000000000 : ℝ)|=(6012871837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008362369/10000000000 : ℝ)|^73 ≤ (12798192046497/100000000000000 : ℝ)^57
        have hw : |(-2008362369/10000000000 : ℝ)|=(2008362369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s3_s3_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1321877571/2000000000 : ℝ)*x 0 + (2908322489/10000000000 : ℝ)*x 1 + (145598411/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321877571/2000000000 : ℝ)^73 ≤ (7355127323037/12500000000000 : ℝ)^57 := by
    have hnat : (1321877571 : ℕ)^73*12500000000000^57 ≤ 7355127323037^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321877571 2000000000 7355127323037 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2908322489/10000000000 : ℝ)^73 ≤ (20562981632819/100000000000000 : ℝ)^57 := by
    have hnat : (2908322489 : ℕ)^73*100000000000000^57 ≤ 20562981632819^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908322489 10000000000 20562981632819 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145598411/500000000 : ℝ)^73 ≤ (823839990687/4000000000000 : ℝ)^57 := by
    have hnat : (145598411 : ℕ)^73*4000000000000^57 ≤ 823839990687^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145598411 500000000 823839990687 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321877571/2000000000 : ℝ), (2908322489/10000000000 : ℝ), (145598411/500000000 : ℝ)] ![(7355127323037/12500000000000 : ℝ), (20562981632819/100000000000000 : ℝ), (823839990687/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321877571/2000000000 : ℝ)|^73 ≤ (7355127323037/12500000000000 : ℝ)^57
        have hw : |(1321877571/2000000000 : ℝ)|=(1321877571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2908322489/10000000000 : ℝ)|^73 ≤ (20562981632819/100000000000000 : ℝ)^57
        have hw : |(2908322489/10000000000 : ℝ)|=(2908322489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145598411/500000000 : ℝ)|^73 ≤ (823839990687/4000000000000 : ℝ)^57
        have hw : |(145598411/500000000 : ℝ)|=(145598411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312053_s3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((39293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9137/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44009/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3991/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3991/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10003/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10003/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19727/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (39293/100000 : ℝ) ^ (9/2 : ℝ) ≤ (1494233080925832551/100000000000000000000 : ℝ) := by
    have hpowers : (39293/100000 : ℝ)^9 ≤ (1494233080925832551/100000000000000000000 : ℝ)^2 := by
      have hnat : (39293 : ℕ)^9*100000000000000000000^2 ≤ 1494233080925832551^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39293 100000 1494233080925832551 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39293/100000 : ℝ)) (X := (1494233080925832551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0a : (101494233080925832551/100000000000000000000 : ℝ) ≤ (10033013918390307/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (101494233080925832551/100000000000000000000 : ℝ)^2 ≤ (10033013918390307/10000000000000000 : ℝ)^9 := by
      have hnat : (101494233080925832551 : ℕ)^2*10000000000000000^9 ≤ 10033013918390307^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101494233080925832551 100000000000000000000 10033013918390307 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033013918390307/10000000000000000 : ℝ)) (X := (101494233080925832551/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0b : (51494233080925832551/50000000000000000000 : ℝ) ≤ (1258206492659283/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (51494233080925832551/50000000000000000000 : ℝ)^2 ≤ (1258206492659283/1250000000000000 : ℝ)^9 := by
      have hnat : (51494233080925832551 : ℕ)^2*1250000000000000^9 ≤ 1258206492659283^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51494233080925832551 50000000000000000000 1258206492659283 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258206492659283/1250000000000000 : ℝ)) (X := (51494233080925832551/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(33013918390307/3929300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(32638022883957/3929300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (39293/100000 : ℝ)) (alpha := (33013918390307/3929300000000000 : ℝ)) (beta := (32638022883957/3929300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39293/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(33013918390307/3929300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(32638022883957/3929300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (9137/20000 : ℝ) ^ (9/2 : ℝ) ≤ (2944295068950667029/100000000000000000000 : ℝ) := by
    have hpowers : (9137/20000 : ℝ)^9 ≤ (2944295068950667029/100000000000000000000 : ℝ)^2 := by
      have hnat : (9137 : ℕ)^9*100000000000000000000^2 ≤ 2944295068950667029^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9137 20000 2944295068950667029 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9137/20000 : ℝ)) (X := (2944295068950667029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1a : (102944295068950667029/100000000000000000000 : ℝ) ≤ (201293848541803/200000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (102944295068950667029/100000000000000000000 : ℝ)^2 ≤ (201293848541803/200000000000000 : ℝ)^9 := by
      have hnat : (102944295068950667029 : ℕ)^2*200000000000000^9 ≤ 201293848541803^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102944295068950667029 100000000000000000000 201293848541803 200000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201293848541803/200000000000000 : ℝ)) (X := (102944295068950667029/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1b : (52944295068950667029/50000000000000000000 : ℝ) ≤ (10127961385673649/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52944295068950667029/50000000000000000000 : ℝ)^2 ≤ (10127961385673649/10000000000000000 : ℝ)^9 := by
      have hnat : (52944295068950667029 : ℕ)^2*10000000000000000^9 ≤ 10127961385673649^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52944295068950667029 50000000000000000000 10127961385673649 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10127961385673649/10000000000000000 : ℝ)) (X := (52944295068950667029/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1293848541803/91370000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(63268958583499/4568500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (9137/20000 : ℝ)) (alpha := (1293848541803/91370000000000 : ℝ)) (beta := (63268958583499/4568500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9137/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1293848541803/91370000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(63268958583499/4568500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (44009/100000 : ℝ) ^ (9/2 : ℝ) ≤ (497698976121801349/20000000000000000000 : ℝ) := by
    have hpowers : (44009/100000 : ℝ)^9 ≤ (497698976121801349/20000000000000000000 : ℝ)^2 := by
      have hnat : (44009 : ℕ)^9*20000000000000000000^2 ≤ 497698976121801349^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44009 100000 497698976121801349 20000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44009/100000 : ℝ)) (X := (497698976121801349/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2a : (20497698976121801349/20000000000000000000 : ℝ) ≤ (5027386240341679/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (20497698976121801349/20000000000000000000 : ℝ)^2 ≤ (5027386240341679/5000000000000000 : ℝ)^9 := by
      have hnat : (20497698976121801349 : ℕ)^2*5000000000000000^9 ≤ 5027386240341679^9*20000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20497698976121801349 20000000000000000000 5027386240341679 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027386240341679/5000000000000000 : ℝ)) (X := (20497698976121801349/20000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2b : (10497698976121801349/10000000000000000000 : ℝ) ≤ (5054260075006517/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (10497698976121801349/10000000000000000000 : ℝ)^2 ≤ (5054260075006517/5000000000000000 : ℝ)^9 := by
      have hnat : (10497698976121801349 : ℕ)^2*5000000000000000^9 ≤ 5054260075006517^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10497698976121801349 10000000000000000000 5054260075006517 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054260075006517/5000000000000000 : ℝ)) (X := (10497698976121801349/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27386240341679/2200450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1919559618917/157175000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (44009/100000 : ℝ)) (alpha := (27386240341679/2200450000000000 : ℝ)) (beta := (1919559618917/157175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44009/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27386240341679/2200450000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1919559618917/157175000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2556492533/10000000000 : ℝ)*X 0 0+(2503712099/5000000000 : ℝ)*X 0 1+(2508048261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4479832797/10000000000 : ℝ)*X 1 0+(-129375131/625000000 : ℝ)*X 1 1+(5905510543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2246036023/5000000000 : ℝ)*X 2 0+(5900128963/10000000000 : ℝ)*X 2 1+(-2062012903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1284526247/2000000000 : ℝ)*X 0 0+(3033672913/10000000000 : ℝ)*X 0 1+(1509745679/5000000000 : ℝ)*X 0 2+(1284526247/2000000000 : ℝ)*X 1 0+(3033672913/10000000000 : ℝ)*X 1 1+(1509745679/5000000000 : ℝ)*X 1 2+(1284526247/2000000000 : ℝ)*X 2 0+(3033672913/10000000000 : ℝ)*X 2 1+(1509745679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-319178829/1250000000 : ℝ)*X 0 0+(2428113209/5000000000 : ℝ)*X 0 1+(323029031/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4449460969/10000000000 : ℝ)*X 1 0+(-401368049/2000000000 : ℝ)*X 1 1+(5980313767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4461701761/10000000000 : ℝ)*X 2 0+(241573023/400000000 : ℝ)*X 2 1+(-1910584333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((100229347/156250000 : ℝ)*X 0 0+(803363083/2500000000 : ℝ)*X 0 1+(2846414809/10000000000 : ℝ)*X 0 2+(100229347/156250000 : ℝ)*X 1 0+(803363083/2500000000 : ℝ)*X 1 1+(2846414809/10000000000 : ℝ)*X 1 2+(100229347/156250000 : ℝ)*X 2 0+(803363083/2500000000 : ℝ)*X 2 1+(2846414809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1205243033/5000000000 : ℝ)*X 0 0+(1247725889/2500000000 : ℝ)*X 0 1+(2575972279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((881493317/2000000000 : ℝ)*X 1 0+(-408717881/2000000000 : ℝ)*X 1 1+(18724349/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((4639014173/10000000000 : ℝ)*X 2 0+(586285709/1000000000 : ℝ)*X 2 1+(-1927104243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1318646581/2000000000 : ℝ)*X 0 0+(755017327/2500000000 : ℝ)*X 0 1+(2819576417/10000000000 : ℝ)*X 0 2+(1318646581/2000000000 : ℝ)*X 1 0+(755017327/2500000000 : ℝ)*X 1 1+(2819576417/10000000000 : ℝ)*X 1 2+(1318646581/2000000000 : ℝ)*X 2 0+(755017327/2500000000 : ℝ)*X 2 1+(2819576417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1198205093/5000000000 : ℝ)*X 0 0+(1014596127/2000000000 : ℝ)*X 0 1+(508163759/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((464084919/1000000000 : ℝ)*X 1 0+(-389406829/2000000000 : ℝ)*X 1 1+(182703983/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((137899949/312500000 : ℝ)*X 2 0+(6012871837/10000000000 : ℝ)*X 2 1+(-2008362369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1321877571/2000000000 : ℝ)*X 0 0+(2908322489/10000000000 : ℝ)*X 0 1+(145598411/500000000 : ℝ)*X 0 2+(1321877571/2000000000 : ℝ)*X 1 0+(2908322489/10000000000 : ℝ)*X 1 1+(145598411/500000000 : ℝ)*X 1 2+(1321877571/2000000000 : ℝ)*X 2 0+(2908322489/10000000000 : ℝ)*X 2 1+(145598411/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3991/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3991/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (79027426563994804927298622238203/3950029346317250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1518134666777/500000000000 : ℝ)*(base49) + (762336003481/200000000000 : ℝ)*(base59) + (1625129/1000000000000 : ℝ)*(base60) + (33155787941207/1000000000000 : ℝ)*(major_s3_0) + (33155787941207/1000000000000 : ℝ)*(major_s3_1) + (33155787941207/1000000000000 : ℝ)*(major_s3_2) + (3315439/5000000000 : ℝ)*(sp_s3_0) + (138819193/1000000000000 : ℝ)*(sp_s3_6) + (46446792520857/1000000000000 : ℝ)*(sp_s3_7) + (11611518564741/250000000000 : ℝ)*(sp_s3_8) + (23222969000793/500000000000 : ℝ)*(sp_s3_9) + (19863974785623/1000000000000 : ℝ)*(sp_s3_13) + (1381349693/1000000000000 : ℝ)*(sp_s3_15) + (47425221/31250000000 : ℝ)*(sp_s3_23) + (1241507100301/62500000000 : ℝ)*(f.failure) + (23223727804329/500000000000 : ℝ)*(f.sum) + (185760438202373731/20105511650000000000000000000000 : ℝ)*base63 + (201167159571477/314350000000000000000000000 : ℝ)*base65 + (4582261363861657/4568500000000000000000000000 : ℝ)*base67 + (1701949188300853/2200450000000000000000000000 : ℝ)*base69 + (588447447416077661/4940701820000000000000000000000 : ℝ)*base70 + (2867443973590129/3929300000000000000000000000 : ℝ)*base73 + (1247726026189/5710625000000000000000000 : ℝ)*base75 + (538426884361679/3929300000000000000000000000 : ℝ)*base77 + (9473653645770279527/22438758812500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (2937/6250000000000000 : ℝ)*base86 + (2937/6250000000000000 : ℝ)*base88 + (2937/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10003/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10003/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27528501656761474600012743/2470350910000000000000000000000 : ℝ) := by norm_num
    linear_combination (155421175219/50000000000 : ℝ)*(base49) + (330497461427/100000000000 : ℝ)*(base59) + (6509957047319/200000000000 : ℝ)*(major_s3_0) + (6509957047319/200000000000 : ℝ)*(major_s3_1) + (6509957047319/200000000000 : ℝ)*(major_s3_2) + (564000379/1000000000000 : ℝ)*(sp_s3_1) + (20499799/125000000000 : ℝ)*(sp_s3_2) + (46256337/250000000000 : ℝ)*(sp_s3_6) + (169194137/500000000000 : ℝ)*(sp_s3_7) + (45598179778253/1000000000000 : ℝ)*(sp_s3_14) + (11399488541537/250000000000 : ℝ)*(sp_s3_15) + (9119670833627/200000000000 : ℝ)*(sp_s3_16) + (19500486386111/1000000000000 : ℝ)*(sp_s3_20) + (377180679/1000000000000 : ℝ)*(sp_s3_27) + (9750524296069/500000000000 : ℝ)*(f.failure) + (45598518166527/1000000000000 : ℝ)*(f.sum) + (4329703320426359/25131889562500000000000000000 : ℝ)*base63 + (64621354486087/62870000000000000000000000 : ℝ)*base64 + (563568548899911/913700000000000000000000000 : ℝ)*base66 + (138722008841103/220045000000000000000000000 : ℝ)*base68 + (1057836282827787843/4940701820000000000000000000000 : ℝ)*base70 + (115449386795577/157172000000000000000000000 : ℝ)*base72 + (29103107220547/45685000000000000000000000 : ℝ)*base74 + (570311830414221/785860000000000000000000000 : ℝ)*base76 + (3620752697312836061/17951007050000000000000000000000 : ℝ)*base79 + (14997/50000000000000000 : ℝ)*base87 + (14997/50000000000000000 : ℝ)*base89 + (14997/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19727/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8520173638632426305273900848569/564289906616750000000000000000000000 : ℝ) := by norm_num
    linear_combination (242840879239/1000000000000 : ℝ)*(base40) + (138392978337/50000000000 : ℝ)*(base49) + (3056224418073/1000000000000 : ℝ)*(base59) + (29707125343397/1000000000000 : ℝ)*(major_s3_0) + (29707125343397/1000000000000 : ℝ)*(major_s3_1) + (29707125343397/1000000000000 : ℝ)*(major_s3_2) + (11450607/50000000000 : ℝ)*(sp_s3_0) + (232215003/500000000000 : ℝ)*(sp_s3_2) + (108435619/1000000000000 : ℝ)*(sp_s3_9) + (586096539/500000000000 : ℝ)*(sp_s3_20) + (4161604683501/100000000000 : ℝ)*(sp_s3_21) + (832325516943/20000000000 : ℝ)*(sp_s3_22) + (1664628119261/40000000000 : ℝ)*(sp_s3_23) + (8898398806793/500000000000 : ℝ)*(sp_s3_27) + (2224746225833/125000000000 : ℝ)*(f.failure) + (832325516943/20000000000 : ℝ)*(f.sum) + (1046493379027476313/10052755825000000000000000000000 : ℝ)*base63 + (115410027575989/157175000000000000000000000 : ℝ)*base64 + (312393737725797/4568500000000000000000000000 : ℝ)*base67 + (599602599071837/2200450000000000000000000000 : ℝ)*base68 + (2793801535284707327/4940701820000000000000000000000 : ℝ)*base70 + (512860007276851/3929300000000000000000000000 : ℝ)*base72 + (6234126339361/22842500000000000000000000 : ℝ)*base74 + (2112604380035701/3929300000000000000000000000 : ℝ)*base76 + (59270353951242965193/89755035250000000000000000000000 : ℝ)*base79 + (1029/12500000000000000 : ℝ)*base87 + (1029/12500000000000000 : ℝ)*base89 + (1029/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((39293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9137/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44009/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3991/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3991/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10003/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10003/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19727/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312053_s3 p hpa hpb X hX hprev2

#print axioms solution
