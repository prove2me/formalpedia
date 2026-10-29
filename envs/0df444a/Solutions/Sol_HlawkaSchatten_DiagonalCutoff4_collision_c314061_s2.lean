-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:48.46499+00:00
-- url     : https://prove2.me/submissions/4374cb87-33a1-49b1-8bc0-723172b53f9c

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
theorem collision_support_c314061_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026780071/10000000000 : ℝ)*x 0 + (4492176553/10000000000 : ℝ)*x 1 + (5860098793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026780071/10000000000 : ℝ)^75 ≤ (6573429139037/50000000000000 : ℝ)^59 := by
    have hnat : (2026780071 : ℕ)^75*50000000000000^59 ≤ 6573429139037^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026780071 10000000000 6573429139037 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492176553/10000000000 : ℝ)^75 ≤ (7231656905037/20000000000000 : ℝ)^59 := by
    have hnat : (4492176553 : ℕ)^75*20000000000000^59 ≤ 7231656905037^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492176553 10000000000 7231656905037 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5860098793/10000000000 : ℝ)^75 ≤ (50694857173411/100000000000000 : ℝ)^59 := by
    have hnat : (5860098793 : ℕ)^75*100000000000000^59 ≤ 50694857173411^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5860098793 10000000000 50694857173411 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026780071/10000000000 : ℝ), (4492176553/10000000000 : ℝ), (5860098793/10000000000 : ℝ)] ![(6573429139037/50000000000000 : ℝ), (7231656905037/20000000000000 : ℝ), (50694857173411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026780071/10000000000 : ℝ)|^75 ≤ (6573429139037/50000000000000 : ℝ)^59
        have hw : |(-2026780071/10000000000 : ℝ)|=(2026780071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492176553/10000000000 : ℝ)|^75 ≤ (7231656905037/20000000000000 : ℝ)^59
        have hw : |(4492176553/10000000000 : ℝ)|=(4492176553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5860098793/10000000000 : ℝ)|^75 ≤ (50694857173411/100000000000000 : ℝ)^59
        have hw : |(5860098793/10000000000 : ℝ)|=(5860098793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2375285609/5000000000 : ℝ)*x 0 + (78431481/125000000 : ℝ)*x 1 + (-67286257/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2375285609/5000000000 : ℝ)^75 ≤ (38822516772203/100000000000000 : ℝ)^59 := by
    have hnat : (2375285609 : ℕ)^75*100000000000000^59 ≤ 38822516772203^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375285609 5000000000 38822516772203 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78431481/125000000 : ℝ)^75 ≤ (55295138811261/100000000000000 : ℝ)^59 := by
    have hnat : (78431481 : ℕ)^75*100000000000000^59 ≤ 55295138811261^59*125000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78431481 125000000 55295138811261 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67286257/625000000 : ℝ)^75 ≤ (5882344404297/100000000000000 : ℝ)^59 := by
    have hnat : (67286257 : ℕ)^75*100000000000000^59 ≤ 5882344404297^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67286257 625000000 5882344404297 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2375285609/5000000000 : ℝ), (78431481/125000000 : ℝ), (-67286257/625000000 : ℝ)] ![(38822516772203/100000000000000 : ℝ), (55295138811261/100000000000000 : ℝ), (5882344404297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2375285609/5000000000 : ℝ)|^75 ≤ (38822516772203/100000000000000 : ℝ)^59
        have hw : |(2375285609/5000000000 : ℝ)|=(2375285609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78431481/125000000 : ℝ)|^75 ≤ (55295138811261/100000000000000 : ℝ)^59
        have hw : |(78431481/125000000 : ℝ)|=(78431481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67286257/625000000 : ℝ)|^75 ≤ (5882344404297/100000000000000 : ℝ)^59
        have hw : |(-67286257/625000000 : ℝ)|=(67286257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (619979239/1000000000 : ℝ)*x 0 + (2826146399/10000000000 : ℝ)*x 1 + (53294639/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (619979239/1000000000 : ℝ)^75 ≤ (27229686949909/50000000000000 : ℝ)^59 := by
    have hnat : (619979239 : ℕ)^75*50000000000000^59 ≤ 27229686949909^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619979239 1000000000 27229686949909 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2826146399/10000000000 : ℝ)^75 ≤ (20061624032241/100000000000000 : ℝ)^59 := by
    have hnat : (2826146399 : ℕ)^75*100000000000000^59 ≤ 20061624032241^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826146399 10000000000 20061624032241 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53294639/156250000 : ℝ)^75 ≤ (12739501023487/50000000000000 : ℝ)^59 := by
    have hnat : (53294639 : ℕ)^75*50000000000000^59 ≤ 12739501023487^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53294639 156250000 12739501023487 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(619979239/1000000000 : ℝ), (2826146399/10000000000 : ℝ), (53294639/156250000 : ℝ)] ![(27229686949909/50000000000000 : ℝ), (20061624032241/100000000000000 : ℝ), (12739501023487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(619979239/1000000000 : ℝ)|^75 ≤ (27229686949909/50000000000000 : ℝ)^59
        have hw : |(619979239/1000000000 : ℝ)|=(619979239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2826146399/10000000000 : ℝ)|^75 ≤ (20061624032241/100000000000000 : ℝ)^59
        have hw : |(2826146399/10000000000 : ℝ)|=(2826146399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53294639/156250000 : ℝ)|^75 ≤ (12739501023487/50000000000000 : ℝ)^59
        have hw : |(53294639/156250000 : ℝ)|=(53294639/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016424887/10000000000 : ℝ)*x 0 + (769494191/2000000000 : ℝ)*x 1 + (3223904847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016424887/10000000000 : ℝ)^75 ≤ (522461293511/4000000000000 : ℝ)^59 := by
    have hnat : (2016424887 : ℕ)^75*4000000000000^59 ≤ 522461293511^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016424887 10000000000 522461293511 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769494191/2000000000 : ℝ)^75 ≤ (29694808551157/100000000000000 : ℝ)^59 := by
    have hnat : (769494191 : ℕ)^75*100000000000000^59 ≤ 29694808551157^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769494191 2000000000 29694808551157 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3223904847/5000000000 : ℝ)^75 ≤ (11448731818931/20000000000000 : ℝ)^59 := by
    have hnat : (3223904847 : ℕ)^75*20000000000000^59 ≤ 11448731818931^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3223904847 5000000000 11448731818931 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016424887/10000000000 : ℝ), (769494191/2000000000 : ℝ), (3223904847/5000000000 : ℝ)] ![(522461293511/4000000000000 : ℝ), (29694808551157/100000000000000 : ℝ), (11448731818931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016424887/10000000000 : ℝ)|^75 ≤ (522461293511/4000000000000 : ℝ)^59
        have hw : |(-2016424887/10000000000 : ℝ)|=(2016424887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769494191/2000000000 : ℝ)|^75 ≤ (29694808551157/100000000000000 : ℝ)^59
        have hw : |(769494191/2000000000 : ℝ)|=(769494191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3223904847/5000000000 : ℝ)|^75 ≤ (11448731818931/20000000000000 : ℝ)^59
        have hw : |(3223904847/5000000000 : ℝ)|=(3223904847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (426883103/1000000000 : ℝ)*x 0 + (-1521738289/10000000000 : ℝ)*x 1 + (803039359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426883103/1000000000 : ℝ)^75 ≤ (33888611009081/100000000000000 : ℝ)^59 := by
    have hnat : (426883103 : ℕ)^75*100000000000000^59 ≤ 33888611009081^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426883103 1000000000 33888611009081 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521738289/10000000000 : ℝ)^75 ≤ (1141593973573/12500000000000 : ℝ)^59 := by
    have hnat : (1521738289 : ℕ)^75*12500000000000^59 ≤ 1141593973573^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521738289 10000000000 1141593973573 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803039359/1250000000 : ℝ)^75 ≤ (14244659298121/25000000000000 : ℝ)^59 := by
    have hnat : (803039359 : ℕ)^75*25000000000000^59 ≤ 14244659298121^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803039359 1250000000 14244659298121 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426883103/1000000000 : ℝ), (-1521738289/10000000000 : ℝ), (803039359/1250000000 : ℝ)] ![(33888611009081/100000000000000 : ℝ), (1141593973573/12500000000000 : ℝ), (14244659298121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426883103/1000000000 : ℝ)|^75 ≤ (33888611009081/100000000000000 : ℝ)^59
        have hw : |(426883103/1000000000 : ℝ)|=(426883103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1521738289/10000000000 : ℝ)|^75 ≤ (1141593973573/12500000000000 : ℝ)^59
        have hw : |(-1521738289/10000000000 : ℝ)|=(1521738289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803039359/1250000000 : ℝ)|^75 ≤ (14244659298121/25000000000000 : ℝ)^59
        have hw : |(803039359/1250000000 : ℝ)|=(803039359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2169180107/5000000000 : ℝ)*x 0 + (3516302393/5000000000 : ℝ)*x 1 + (-364615343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169180107/5000000000 : ℝ)^75 ≤ (8647951394103/25000000000000 : ℝ)^59 := by
    have hnat : (2169180107 : ℕ)^75*25000000000000^59 ≤ 8647951394103^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169180107 5000000000 8647951394103 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3516302393/5000000000 : ℝ)^75 ≤ (31961430283551/50000000000000 : ℝ)^59 := by
    have hnat : (3516302393 : ℕ)^75*50000000000000^59 ≤ 31961430283551^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3516302393 5000000000 31961430283551 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364615343/10000000000 : ℝ)^75 ≤ (742666920729/50000000000000 : ℝ)^59 := by
    have hnat : (364615343 : ℕ)^75*50000000000000^59 ≤ 742666920729^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364615343 10000000000 742666920729 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169180107/5000000000 : ℝ), (3516302393/5000000000 : ℝ), (-364615343/10000000000 : ℝ)] ![(8647951394103/25000000000000 : ℝ), (31961430283551/50000000000000 : ℝ), (742666920729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169180107/5000000000 : ℝ)|^75 ≤ (8647951394103/25000000000000 : ℝ)^59
        have hw : |(2169180107/5000000000 : ℝ)|=(2169180107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3516302393/5000000000 : ℝ)|^75 ≤ (31961430283551/50000000000000 : ℝ)^59
        have hw : |(3516302393/5000000000 : ℝ)|=(3516302393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364615343/10000000000 : ℝ)|^75 ≤ (742666920729/50000000000000 : ℝ)^59
        have hw : |(-364615343/10000000000 : ℝ)|=(364615343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6132366667/10000000000 : ℝ)*x 0 + (827252027/2000000000 : ℝ)*x 1 + (262235887/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6132366667/10000000000 : ℝ)^75 ≤ (53707599110989/100000000000000 : ℝ)^59 := by
    have hnat : (6132366667 : ℕ)^75*100000000000000^59 ≤ 53707599110989^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6132366667 10000000000 53707599110989 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827252027/2000000000 : ℝ)^75 ≤ (3255645356047/10000000000000 : ℝ)^59 := by
    have hnat : (827252027 : ℕ)^75*10000000000000^59 ≤ 3255645356047^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827252027 2000000000 3255645356047 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262235887/1250000000 : ℝ)^75 ≤ (13735947318219/100000000000000 : ℝ)^59 := by
    have hnat : (262235887 : ℕ)^75*100000000000000^59 ≤ 13735947318219^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262235887 1250000000 13735947318219 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6132366667/10000000000 : ℝ), (827252027/2000000000 : ℝ), (262235887/1250000000 : ℝ)] ![(53707599110989/100000000000000 : ℝ), (3255645356047/10000000000000 : ℝ), (13735947318219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6132366667/10000000000 : ℝ)|^75 ≤ (53707599110989/100000000000000 : ℝ)^59
        have hw : |(6132366667/10000000000 : ℝ)|=(6132366667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827252027/2000000000 : ℝ)|^75 ≤ (3255645356047/10000000000000 : ℝ)^59
        have hw : |(827252027/2000000000 : ℝ)|=(827252027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262235887/1250000000 : ℝ)|^75 ≤ (13735947318219/100000000000000 : ℝ)^59
        have hw : |(262235887/1250000000 : ℝ)|=(262235887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076945651/10000000000 : ℝ)*x 0 + (2285175889/5000000000 : ℝ)*x 1 + (1609989531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076945651/10000000000 : ℝ)^75 ≤ (5884883429777/100000000000000 : ℝ)^59 := by
    have hnat : (1076945651 : ℕ)^75*100000000000000^59 ≤ 5884883429777^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076945651 10000000000 5884883429777 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285175889/5000000000 : ℝ)^75 ≤ (7392010492489/20000000000000 : ℝ)^59 := by
    have hnat : (2285175889 : ℕ)^75*20000000000000^59 ≤ 7392010492489^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285175889 5000000000 7392010492489 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1609989531/2500000000 : ℝ)^75 ≤ (14288766024323/25000000000000 : ℝ)^59 := by
    have hnat : (1609989531 : ℕ)^75*25000000000000^59 ≤ 14288766024323^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609989531 2500000000 14288766024323 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076945651/10000000000 : ℝ), (2285175889/5000000000 : ℝ), (1609989531/2500000000 : ℝ)] ![(5884883429777/100000000000000 : ℝ), (7392010492489/20000000000000 : ℝ), (14288766024323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076945651/10000000000 : ℝ)|^75 ≤ (5884883429777/100000000000000 : ℝ)^59
        have hw : |(-1076945651/10000000000 : ℝ)|=(1076945651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2285175889/5000000000 : ℝ)|^75 ≤ (7392010492489/20000000000000 : ℝ)^59
        have hw : |(2285175889/5000000000 : ℝ)|=(2285175889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1609989531/2500000000 : ℝ)|^75 ≤ (14288766024323/25000000000000 : ℝ)^59
        have hw : |(1609989531/2500000000 : ℝ)|=(1609989531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (839047241/2000000000 : ℝ)*x 0 + (-325888993/2000000000 : ℝ)*x 1 + (6416462263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839047241/2000000000 : ℝ)^75 ≤ (33147675123861/100000000000000 : ℝ)^59 := by
    have hnat : (839047241 : ℕ)^75*100000000000000^59 ≤ 33147675123861^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839047241 2000000000 33147675123861 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325888993/2000000000 : ℝ)^75 ≤ (9962206657321/100000000000000 : ℝ)^59 := by
    have hnat : (325888993 : ℕ)^75*100000000000000^59 ≤ 9962206657321^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325888993 2000000000 9962206657321 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6416462263/10000000000 : ℝ)^75 ≤ (7111264775127/12500000000000 : ℝ)^59 := by
    have hnat : (6416462263 : ℕ)^75*12500000000000^59 ≤ 7111264775127^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6416462263 10000000000 7111264775127 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839047241/2000000000 : ℝ), (-325888993/2000000000 : ℝ), (6416462263/10000000000 : ℝ)] ![(33147675123861/100000000000000 : ℝ), (9962206657321/100000000000000 : ℝ), (7111264775127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839047241/2000000000 : ℝ)|^75 ≤ (33147675123861/100000000000000 : ℝ)^59
        have hw : |(839047241/2000000000 : ℝ)|=(839047241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-325888993/2000000000 : ℝ)|^75 ≤ (9962206657321/100000000000000 : ℝ)^59
        have hw : |(-325888993/2000000000 : ℝ)|=(325888993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6416462263/10000000000 : ℝ)|^75 ≤ (7111264775127/12500000000000 : ℝ)^59
        have hw : |(6416462263/10000000000 : ℝ)|=(6416462263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1151626143/2000000000 : ℝ)*x 0 + (1424011713/2500000000 : ℝ)*x 1 + (-5819809/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1151626143/2000000000 : ℝ)^75 ≤ (3098511664517/6250000000000 : ℝ)^59 := by
    have hnat : (1151626143 : ℕ)^75*6250000000000^59 ≤ 3098511664517^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151626143 2000000000 3098511664517 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424011713/2500000000 : ℝ)^75 ≤ (6112212260179/12500000000000 : ℝ)^59 := by
    have hnat : (1424011713 : ℕ)^75*12500000000000^59 ≤ 6112212260179^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424011713 2500000000 6112212260179 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5819809/156250000 : ℝ)^75 ≤ (763057635037/50000000000000 : ℝ)^59 := by
    have hnat : (5819809 : ℕ)^75*50000000000000^59 ≤ 763057635037^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5819809 156250000 763057635037 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1151626143/2000000000 : ℝ), (1424011713/2500000000 : ℝ), (-5819809/156250000 : ℝ)] ![(3098511664517/6250000000000 : ℝ), (6112212260179/12500000000000 : ℝ), (763057635037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1151626143/2000000000 : ℝ)|^75 ≤ (3098511664517/6250000000000 : ℝ)^59
        have hw : |(1151626143/2000000000 : ℝ)|=(1151626143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424011713/2500000000 : ℝ)|^75 ≤ (6112212260179/12500000000000 : ℝ)^59
        have hw : |(1424011713/2500000000 : ℝ)|=(1424011713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5819809/156250000 : ℝ)|^75 ≤ (763057635037/50000000000000 : ℝ)^59
        have hw : |(-5819809/156250000 : ℝ)|=(5819809/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (116947107/156250000 : ℝ)*x 0 + (77220867/312500000 : ℝ)*x 1 + (1058529181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116947107/156250000 : ℝ)^75 ≤ (6919041248411/10000000000000 : ℝ)^59 := by
    have hnat : (116947107 : ℕ)^75*10000000000000^59 ≤ 6919041248411^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116947107 156250000 6919041248411 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77220867/312500000 : ℝ)^75 ≤ (8456939148147/50000000000000 : ℝ)^59 := by
    have hnat : (77220867 : ℕ)^75*50000000000000^59 ≤ 8456939148147^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77220867 312500000 8456939148147 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058529181/5000000000 : ℝ)^75 ≤ (13895709198291/100000000000000 : ℝ)^59 := by
    have hnat : (1058529181 : ℕ)^75*100000000000000^59 ≤ 13895709198291^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058529181 5000000000 13895709198291 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(116947107/156250000 : ℝ), (77220867/312500000 : ℝ), (1058529181/5000000000 : ℝ)] ![(6919041248411/10000000000000 : ℝ), (8456939148147/50000000000000 : ℝ), (13895709198291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(116947107/156250000 : ℝ)|^75 ≤ (6919041248411/10000000000000 : ℝ)^59
        have hw : |(116947107/156250000 : ℝ)|=(116947107/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77220867/312500000 : ℝ)|^75 ≤ (8456939148147/50000000000000 : ℝ)^59
        have hw : |(77220867/312500000 : ℝ)|=(77220867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058529181/5000000000 : ℝ)|^75 ≤ (13895709198291/100000000000000 : ℝ)^59
        have hw : |(1058529181/5000000000 : ℝ)|=(1058529181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033750049/10000000000 : ℝ)*x 0 + (2626009493/5000000000 : ℝ)*x 1 + (582498697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033750049/10000000000 : ℝ)^75 ≤ (5586481981023/100000000000000 : ℝ)^59 := by
    have hnat : (1033750049 : ℕ)^75*100000000000000^59 ≤ 5586481981023^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033750049 10000000000 5586481981023 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626009493/5000000000 : ℝ)^75 ≤ (44104466055131/100000000000000 : ℝ)^59 := by
    have hnat : (2626009493 : ℕ)^75*100000000000000^59 ≤ 44104466055131^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626009493 5000000000 44104466055131 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582498697/1000000000 : ℝ)^75 ≤ (50309051949819/100000000000000 : ℝ)^59 := by
    have hnat : (582498697 : ℕ)^75*100000000000000^59 ≤ 50309051949819^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582498697 1000000000 50309051949819 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033750049/10000000000 : ℝ), (2626009493/5000000000 : ℝ), (582498697/1000000000 : ℝ)] ![(5586481981023/100000000000000 : ℝ), (44104466055131/100000000000000 : ℝ), (50309051949819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033750049/10000000000 : ℝ)|^75 ≤ (5586481981023/100000000000000 : ℝ)^59
        have hw : |(-1033750049/10000000000 : ℝ)|=(1033750049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626009493/5000000000 : ℝ)|^75 ≤ (44104466055131/100000000000000 : ℝ)^59
        have hw : |(2626009493/5000000000 : ℝ)|=(2626009493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(582498697/1000000000 : ℝ)|^75 ≤ (50309051949819/100000000000000 : ℝ)^59
        have hw : |(582498697/1000000000 : ℝ)|=(582498697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44779669/78125000 : ℝ)*x 0 + (-106659227/1000000000 : ℝ)*x 1 + (2663143157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44779669/78125000 : ℝ)^75 ≤ (49288159851121/100000000000000 : ℝ)^59 := by
    have hnat : (44779669 : ℕ)^75*100000000000000^59 ≤ 49288159851121^59*78125000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44779669 78125000 49288159851121 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106659227/1000000000 : ℝ)^75 ≤ (5813059741353/100000000000000 : ℝ)^59 := by
    have hnat : (106659227 : ℕ)^75*100000000000000^59 ≤ 5813059741353^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106659227 1000000000 5813059741353 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663143157/5000000000 : ℝ)^75 ≤ (22449390201219/50000000000000 : ℝ)^59 := by
    have hnat : (2663143157 : ℕ)^75*50000000000000^59 ≤ 22449390201219^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663143157 5000000000 22449390201219 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44779669/78125000 : ℝ), (-106659227/1000000000 : ℝ), (2663143157/5000000000 : ℝ)] ![(49288159851121/100000000000000 : ℝ), (5813059741353/100000000000000 : ℝ), (22449390201219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44779669/78125000 : ℝ)|^75 ≤ (49288159851121/100000000000000 : ℝ)^59
        have hw : |(44779669/78125000 : ℝ)|=(44779669/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106659227/1000000000 : ℝ)|^75 ≤ (5813059741353/100000000000000 : ℝ)^59
        have hw : |(-106659227/1000000000 : ℝ)|=(106659227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663143157/5000000000 : ℝ)|^75 ≤ (22449390201219/50000000000000 : ℝ)^59
        have hw : |(2663143157/5000000000 : ℝ)|=(2663143157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (827656903/2000000000 : ℝ)*x 0 + (1738294387/2500000000 : ℝ)*x 1 + (-859306683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827656903/2000000000 : ℝ)^75 ≤ (32576709824637/100000000000000 : ℝ)^59 := by
    have hnat : (827656903 : ℕ)^75*100000000000000^59 ≤ 32576709824637^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827656903 2000000000 32576709824637 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738294387/2500000000 : ℝ)^75 ≤ (63006531900841/100000000000000 : ℝ)^59 := by
    have hnat : (1738294387 : ℕ)^75*100000000000000^59 ≤ 63006531900841^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738294387 2500000000 63006531900841 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859306683/10000000000 : ℝ)^75 ≤ (4416758266979/100000000000000 : ℝ)^59 := by
    have hnat : (859306683 : ℕ)^75*100000000000000^59 ≤ 4416758266979^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859306683 10000000000 4416758266979 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827656903/2000000000 : ℝ), (1738294387/2500000000 : ℝ), (-859306683/10000000000 : ℝ)] ![(32576709824637/100000000000000 : ℝ), (63006531900841/100000000000000 : ℝ), (4416758266979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827656903/2000000000 : ℝ)|^75 ≤ (32576709824637/100000000000000 : ℝ)^59
        have hw : |(827656903/2000000000 : ℝ)|=(827656903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1738294387/2500000000 : ℝ)|^75 ≤ (63006531900841/100000000000000 : ℝ)^59
        have hw : |(1738294387/2500000000 : ℝ)|=(1738294387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859306683/10000000000 : ℝ)|^75 ≤ (4416758266979/100000000000000 : ℝ)^59
        have hw : |(-859306683/10000000000 : ℝ)|=(859306683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314061_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1948350221/2500000000 : ℝ)*x 0 + (80492871/400000000 : ℝ)*x 1 + (536364533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1948350221/2500000000 : ℝ)^75 ≤ (72839147028439/100000000000000 : ℝ)^59 := by
    have hnat : (1948350221 : ℕ)^75*100000000000000^59 ≤ 72839147028439^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948350221 2500000000 72839147028439 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80492871/400000000 : ℝ)^75 ≤ (13027755825557/100000000000000 : ℝ)^59 := by
    have hnat : (80492871 : ℕ)^75*100000000000000^59 ≤ 13027755825557^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80492871 400000000 13027755825557 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536364533/2500000000 : ℝ)^75 ≤ (7066548567799/50000000000000 : ℝ)^59 := by
    have hnat : (536364533 : ℕ)^75*50000000000000^59 ≤ 7066548567799^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536364533 2500000000 7066548567799 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1948350221/2500000000 : ℝ), (80492871/400000000 : ℝ), (536364533/2500000000 : ℝ)] ![(72839147028439/100000000000000 : ℝ), (13027755825557/100000000000000 : ℝ), (7066548567799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1948350221/2500000000 : ℝ)|^75 ≤ (72839147028439/100000000000000 : ℝ)^59
        have hw : |(1948350221/2500000000 : ℝ)|=(1948350221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80492871/400000000 : ℝ)|^75 ≤ (13027755825557/100000000000000 : ℝ)^59
        have hw : |(80492871/400000000 : ℝ)|=(80492871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536364533/2500000000 : ℝ)|^75 ≤ (7066548567799/50000000000000 : ℝ)^59
        have hw : |(536364533/2500000000 : ℝ)|=(536364533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314061_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((30849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31811/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31811/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6743/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6743/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19889/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19889/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(907/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(907/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (30849/50000 : ℝ) ^ (37/8 : ℝ) ≤ (214305723159364021/2000000000000000000 : ℝ) := by
    have hpowers : (30849/50000 : ℝ)^37 ≤ (214305723159364021/2000000000000000000 : ℝ)^8 := by
      have hnat : (30849 : ℕ)^37*2000000000000000000^8 ≤ 214305723159364021^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30849 50000 214305723159364021 2000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30849/50000 : ℝ)) (X := (214305723159364021/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (2214305723159364021/2000000000000000000 : ℝ) ≤ (2044506016063949/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2214305723159364021/2000000000000000000 : ℝ)^8 ≤ (2044506016063949/2000000000000000 : ℝ)^37 := by
      have hnat : (2214305723159364021 : ℕ)^8*2000000000000000^37 ≤ 2044506016063949^37*2000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2214305723159364021 2000000000000000000 2044506016063949 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2044506016063949/2000000000000000 : ℝ)) (X := (2214305723159364021/2000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (1214305723159364021/1000000000000000000 : ℝ) ≤ (10428770016095359/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1214305723159364021/1000000000000000000 : ℝ)^8 ≤ (10428770016095359/10000000000000000 : ℝ)^37 := by
      have hnat : (1214305723159364021 : ℕ)^8*10000000000000000^37 ≤ 10428770016095359^37*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1214305723159364021 1000000000000000000 10428770016095359 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10428770016095359/10000000000000000 : ℝ)) (X := (1214305723159364021/1000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14835338687983/411320000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2644101740713/79100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (30849/50000 : ℝ)) (alpha := (14835338687983/411320000000000 : ℝ)) (beta := (2644101740713/79100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30849/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14835338687983/411320000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2644101740713/79100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (31811/50000 : ℝ) ^ (37/8 : ℝ) ≤ (98803841339486367/800000000000000000 : ℝ) := by
    have hpowers : (31811/50000 : ℝ)^37 ≤ (98803841339486367/800000000000000000 : ℝ)^8 := by
      have hnat : (31811 : ℕ)^37*800000000000000000^8 ≤ 98803841339486367^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31811 50000 98803841339486367 800000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31811/50000 : ℝ)) (X := (98803841339486367/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (898803841339486367/800000000000000000 : ℝ) ≤ (10254987152510657/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (898803841339486367/800000000000000000 : ℝ)^8 ≤ (10254987152510657/10000000000000000 : ℝ)^37 := by
      have hnat : (898803841339486367 : ℕ)^8*10000000000000000^37 ≤ 10254987152510657^37*800000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        898803841339486367 800000000000000000 10254987152510657 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10254987152510657/10000000000000000 : ℝ)) (X := (898803841339486367/800000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (498803841339486367/400000000000000000 : ℝ) ≤ (5244433819247053/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (498803841339486367/400000000000000000 : ℝ)^8 ≤ (5244433819247053/5000000000000000 : ℝ)^37 := by
      have hnat : (498803841339486367 : ℕ)^8*5000000000000000^37 ≤ 5244433819247053^37*400000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        498803841339486367 400000000000000000 5244433819247053 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5244433819247053/5000000000000000 : ℝ)) (X := (498803841339486367/400000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(254987152510657/6362200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(233880485983449/6362200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (31811/50000 : ℝ)) (alpha := (254987152510657/6362200000000000 : ℝ)) (beta := (233880485983449/6362200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (31811/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(254987152510657/6362200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(233880485983449/6362200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (58623/100000 : ℝ) ^ (37/8 : ℝ) ≤ (1691783083875601519/20000000000000000000 : ℝ) := by
    have hpowers : (58623/100000 : ℝ)^37 ≤ (1691783083875601519/20000000000000000000 : ℝ)^8 := by
      have hnat : (58623 : ℕ)^37*20000000000000000000^8 ≤ 1691783083875601519^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58623 100000 1691783083875601519 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58623/100000 : ℝ)) (X := (1691783083875601519/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (21691783083875601519/20000000000000000000 : ℝ) ≤ (10177120588109881/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (21691783083875601519/20000000000000000000 : ℝ)^8 ≤ (10177120588109881/10000000000000000 : ℝ)^37 := by
      have hnat : (21691783083875601519 : ℕ)^8*10000000000000000^37 ≤ 10177120588109881^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21691783083875601519 20000000000000000000 10177120588109881 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10177120588109881/10000000000000000 : ℝ)) (X := (21691783083875601519/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (11691783083875601519/10000000000000000000 : ℝ) ≤ (2068744776014731/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (11691783083875601519/10000000000000000000 : ℝ)^8 ≤ (2068744776014731/2000000000000000 : ℝ)^37 := by
      have hnat : (11691783083875601519 : ℕ)^8*2000000000000000^37 ≤ 2068744776014731^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11691783083875601519 10000000000000000000 2068744776014731 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2068744776014731/2000000000000000 : ℝ)) (X := (11691783083875601519/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(59040196036627/1954100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(83301645981887/2931150000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (58623/100000 : ℝ)) (alpha := (59040196036627/1954100000000000 : ℝ)) (beta := (83301645981887/2931150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (58623/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(59040196036627/1954100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(83301645981887/2931150000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2026780071/10000000000 : ℝ)*X 0 0+(4492176553/10000000000 : ℝ)*X 0 1+(5860098793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2375285609/5000000000 : ℝ)*X 2 0+(78431481/125000000 : ℝ)*X 2 1+(-67286257/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((619979239/1000000000 : ℝ)*X 0 0+(2826146399/10000000000 : ℝ)*X 0 1+(53294639/156250000 : ℝ)*X 0 2+(619979239/1000000000 : ℝ)*X 1 0+(2826146399/10000000000 : ℝ)*X 1 1+(53294639/156250000 : ℝ)*X 1 2+(619979239/1000000000 : ℝ)*X 2 0+(2826146399/10000000000 : ℝ)*X 2 1+(53294639/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2016424887/10000000000 : ℝ)*X 0 0+(769494191/2000000000 : ℝ)*X 0 1+(3223904847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((426883103/1000000000 : ℝ)*X 1 0+(-1521738289/10000000000 : ℝ)*X 1 1+(803039359/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2169180107/5000000000 : ℝ)*X 2 0+(3516302393/5000000000 : ℝ)*X 2 1+(-364615343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((6132366667/10000000000 : ℝ)*X 0 0+(827252027/2000000000 : ℝ)*X 0 1+(262235887/1250000000 : ℝ)*X 0 2+(6132366667/10000000000 : ℝ)*X 1 0+(827252027/2000000000 : ℝ)*X 1 1+(262235887/1250000000 : ℝ)*X 1 2+(6132366667/10000000000 : ℝ)*X 2 0+(827252027/2000000000 : ℝ)*X 2 1+(262235887/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1076945651/10000000000 : ℝ)*X 0 0+(2285175889/5000000000 : ℝ)*X 0 1+(1609989531/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((839047241/2000000000 : ℝ)*X 1 0+(-325888993/2000000000 : ℝ)*X 1 1+(6416462263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1151626143/2000000000 : ℝ)*X 2 0+(1424011713/2500000000 : ℝ)*X 2 1+(-5819809/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((116947107/156250000 : ℝ)*X 0 0+(77220867/312500000 : ℝ)*X 0 1+(1058529181/5000000000 : ℝ)*X 0 2+(116947107/156250000 : ℝ)*X 1 0+(77220867/312500000 : ℝ)*X 1 1+(1058529181/5000000000 : ℝ)*X 1 2+(116947107/156250000 : ℝ)*X 2 0+(77220867/312500000 : ℝ)*X 2 1+(1058529181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1033750049/10000000000 : ℝ)*X 0 0+(2626009493/5000000000 : ℝ)*X 0 1+(582498697/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((44779669/78125000 : ℝ)*X 1 0+(-106659227/1000000000 : ℝ)*X 1 1+(2663143157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((827656903/2000000000 : ℝ)*X 2 0+(1738294387/2500000000 : ℝ)*X 2 1+(-859306683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1948350221/2500000000 : ℝ)*X 0 0+(80492871/400000000 : ℝ)*X 0 1+(536364533/2500000000 : ℝ)*X 0 2+(1948350221/2500000000 : ℝ)*X 1 0+(80492871/400000000 : ℝ)*X 1 1+(536364533/2500000000 : ℝ)*X 1 2+(1948350221/2500000000 : ℝ)*X 2 0+(80492871/400000000 : ℝ)*X 2 1+(536364533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((6743/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6743/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (402940125800331801531661439973/24585021602050000000000000000000000 : ℝ) := by norm_num
    linear_combination (5129869/1000000000000 : ℝ)*(base23) + (58763/40000000000 : ℝ)*(base50) + (916768573169/1000000000000 : ℝ)*(base59) + (4947378559377/1000000000000 : ℝ)*(major_s2_0) + (4947378559377/1000000000000 : ℝ)*(major_s2_1) + (4947378559377/1000000000000 : ℝ)*(major_s2_2) + (28014981/1000000000000 : ℝ)*(sp_s2_0) + (30769511/1000000000000 : ℝ)*(sp_s2_6) + (7019494192259/1000000000000 : ℝ)*(sp_s2_7) + (7018763841947/1000000000000 : ℝ)*(sp_s2_8) + (3509699331973/500000000000 : ℝ)*(sp_s2_9) + (1437599339389/500000000000 : ℝ)*(sp_s2_13) + (758365293/1000000000000 : ℝ)*(sp_s2_15) + (4736537/40000000000 : ℝ)*(sp_s2_23) + (2875229448289/1000000000000 : ℝ)*(f.failure) + (175488055181/25000000000 : ℝ)*(f.sum) + (17745965579429638153/124323750200000000000000000000000 : ℝ)*base62 + (156162610447909/488525000000000000000000000 : ℝ)*base64 + (2862871888814213/6362200000000000000000000000 : ℝ)*base67 + (329390960853069/1954100000000000000000000000 : ℝ)*base69 + (9497973587953004361/40188020600000000000000000000000 : ℝ)*base70 + (6159186554631/79100000000000000000000000 : ℝ)*base73 + (1526580698437011/6362200000000000000000000000 : ℝ)*base74 + (41113926486091/411320000000000000000000000 : ℝ)*base77 + (527759543848664469/1006500040000000000000000000000 : ℝ)*base79 + (60059/100000000000000000 : ℝ)*base86 + (60059/100000000000000000 : ℝ)*base88 + (60059/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19889/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19889/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22149901189433812403671668661/1966801728164000000000000000000000 : ℝ) := by norm_num
    linear_combination (46951/100000000000 : ℝ)*(base39) + (406839/500000000000 : ℝ)*(base49) + (22472667659/50000000000 : ℝ)*(base59) + (4719568768259/1000000000000 : ℝ)*(major_s2_0) + (4719568768259/1000000000000 : ℝ)*(major_s2_1) + (4719568768259/1000000000000 : ℝ)*(major_s2_2) + (49841/2000000000 : ℝ)*(sp_s2_2) + (9395203/500000000000 : ℝ)*(sp_s2_6) + (13966693/250000000000 : ℝ)*(sp_s2_7) + (6696242908741/1000000000000 : ℝ)*(sp_s2_14) + (6696298775513/1000000000000 : ℝ)*(sp_s2_15) + (6696273855013/1000000000000 : ℝ)*(sp_s2_16) + (342835855391/125000000000 : ℝ)*(sp_s2_20) + (129373503/1000000000000 : ℝ)*(sp_s2_27) + (2742835007037/1000000000000 : ℝ)*(f.failure) + (6696298775513/1000000000000 : ℝ)*(f.sum) + (31973066279797046009/124323750200000000000000000000000 : ℝ)*base63 + (133223504573779/366393750000000000000000000 : ℝ)*base65 + (742053222310091/6362200000000000000000000000 : ℝ)*base67 + (510736269449983/1954100000000000000000000000 : ℝ)*base69 + (38026324752452839819/120564061800000000000000000000000 : ℝ)*base71 + (39984376671097/79100000000000000000000000 : ℝ)*base73 + (1482462840457343/6362200000000000000000000000 : ℝ)*base75 + (21955075971833/411320000000000000000000000 : ℝ)*base77 + (639790500883013731/1006500040000000000000000000000 : ℝ)*base79 + (50447/100000000000000000 : ℝ)*base86 + (50447/100000000000000000 : ℝ)*base88 + (50447/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(907/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(907/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4866916227947451864207939349/435133125700000000000000000000000 : ℝ) := by norm_num
    linear_combination (6270863/1000000000000 : ℝ)*(base15) + (57150312713/200000000000 : ℝ)*(base40) + (463864678873/1000000000000 : ℝ)*(base59) + (4238086632257/1000000000000 : ℝ)*(major_s2_0) + (4238086632257/1000000000000 : ℝ)*(major_s2_1) + (4238086632257/1000000000000 : ℝ)*(major_s2_2) + (1470621/1000000000000 : ℝ)*(sp_s2_0) + (113263903/500000000000 : ℝ)*(sp_s2_2) + (64549277/1000000000000 : ℝ)*(sp_s2_9) + (220316337/500000000000 : ℝ)*(sp_s2_20) + (751644034989/125000000000 : ℝ)*(sp_s2_21) + (6013147479671/1000000000000 : ℝ)*(sp_s2_22) + (6012862673451/1000000000000 : ℝ)*(sp_s2_23) + (2462575153003/1000000000000 : ℝ)*(sp_s2_27) + (2463015785677/1000000000000 : ℝ)*(f.failure) + (6013153750533/1000000000000 : ℝ)*(f.sum) + (12113205513134326267/124323750200000000000000000000000 : ℝ)*base63 + (292436736885949/2931150000000000000000000000 : ℝ)*base64 + (2706269506697453/6362200000000000000000000000 : ℝ)*base67 + (309403169426021/1954100000000000000000000000 : ℝ)*base68 + (95482184321775977003/120564061800000000000000000000000 : ℝ)*base70 + (31999880532261/79100000000000000000000000 : ℝ)*base73 + (102412373342749/6362200000000000000000000000 : ℝ)*base75 + (240121159533461/411320000000000000000000000 : ℝ)*base76 + (482265574390166881/1006500040000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (44287/100000000000000000 : ℝ)*base86 + (44287/100000000000000000 : ℝ)*base88 + (44287/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((30849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31811/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31811/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6743/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6743/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19889/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19889/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(907/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(907/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314061_s2 p hpa hpb X hX hprev1

#print axioms solution
