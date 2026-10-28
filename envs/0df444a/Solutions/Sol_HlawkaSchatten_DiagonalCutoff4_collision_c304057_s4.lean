-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304057_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:47.509982+00:00
-- url     : https://prove2.me/submissions/5f2b4b03-e7c7-4f28-b95a-ba5bedd141c0

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
theorem collision_support_c304057_s4_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-106389299/312500000 : ℝ)*x 0 + (170218297/500000000 : ℝ)*x 1 + (1512701039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106389299/312500000 : ℝ)^133 ≤ (12099178574567/50000000000000 : ℝ)^101 := by
    have hnat : (106389299 : ℕ)^133*50000000000000^101 ≤ 12099178574567^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106389299 312500000 12099178574567 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170218297/500000000 : ℝ)^133 ≤ (3024687441221/12500000000000 : ℝ)^101 := by
    have hnat : (170218297 : ℕ)^133*12500000000000^101 ≤ 3024687441221^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170218297 500000000 3024687441221 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512701039/2500000000 : ℝ)^133 ≤ (6450517913799/12500000000000 : ℝ)^101 := by
    have hnat : (1512701039 : ℕ)^133*12500000000000^101 ≤ 6450517913799^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512701039 2500000000 6450517913799 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106389299/312500000 : ℝ), (170218297/500000000 : ℝ), (1512701039/2500000000 : ℝ)] ![(12099178574567/50000000000000 : ℝ), (3024687441221/12500000000000 : ℝ), (6450517913799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106389299/312500000 : ℝ)|^133 ≤ (12099178574567/50000000000000 : ℝ)^101
        have hw : |(-106389299/312500000 : ℝ)|=(106389299/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170218297/500000000 : ℝ)|^133 ≤ (3024687441221/12500000000000 : ℝ)^101
        have hw : |(170218297/500000000 : ℝ)|=(170218297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1512701039/2500000000 : ℝ)|^133 ≤ (6450517913799/12500000000000 : ℝ)^101
        have hw : |(1512701039/2500000000 : ℝ)|=(1512701039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3404379297/10000000000 : ℝ)*x 0 + (-3404287671/10000000000 : ℝ)*x 1 + (6050934619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3404379297/10000000000 : ℝ)^133 ≤ (4839524909621/20000000000000 : ℝ)^101 := by
    have hnat : (3404379297 : ℕ)^133*20000000000000^101 ≤ 4839524909621^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3404379297 10000000000 4839524909621 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3404287671/10000000000 : ℝ)^133 ≤ (4839353390741/20000000000000 : ℝ)^101 := by
    have hnat : (3404287671 : ℕ)^133*20000000000000^101 ≤ 4839353390741^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3404287671 10000000000 4839353390741 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6050934619/10000000000 : ℝ)^133 ≤ (25802804244531/50000000000000 : ℝ)^101 := by
    have hnat : (6050934619 : ℕ)^133*50000000000000^101 ≤ 25802804244531^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6050934619 10000000000 25802804244531 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3404379297/10000000000 : ℝ), (-3404287671/10000000000 : ℝ), (6050934619/10000000000 : ℝ)] ![(4839524909621/20000000000000 : ℝ), (4839353390741/20000000000000 : ℝ), (25802804244531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3404379297/10000000000 : ℝ)|^133 ≤ (4839524909621/20000000000000 : ℝ)^101
        have hw : |(3404379297/10000000000 : ℝ)|=(3404379297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3404287671/10000000000 : ℝ)|^133 ≤ (4839353390741/20000000000000 : ℝ)^101
        have hw : |(-3404287671/10000000000 : ℝ)|=(3404287671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6050934619/10000000000 : ℝ)|^133 ≤ (25802804244531/50000000000000 : ℝ)^101
        have hw : |(6050934619/10000000000 : ℝ)|=(6050934619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2305512561/5000000000 : ℝ)*x 0 + (2305564729/5000000000 : ℝ)*x 1 + (946645937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2305512561/5000000000 : ℝ)^133 ≤ (9020235773337/25000000000000 : ℝ)^101 := by
    have hnat : (2305512561 : ℕ)^133*25000000000000^101 ≤ 9020235773337^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305512561 5000000000 9020235773337 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305564729/5000000000 : ℝ)^133 ≤ (9020504546813/25000000000000 : ℝ)^101 := by
    have hnat : (2305564729 : ℕ)^133*25000000000000^101 ≤ 9020504546813^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305564729 5000000000 9020504546813 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946645937/2500000000 : ℝ)^133 ≤ (27837038699707/100000000000000 : ℝ)^101 := by
    have hnat : (946645937 : ℕ)^133*100000000000000^101 ≤ 27837038699707^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946645937 2500000000 27837038699707 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2305512561/5000000000 : ℝ), (2305564729/5000000000 : ℝ), (946645937/2500000000 : ℝ)] ![(9020235773337/25000000000000 : ℝ), (9020504546813/25000000000000 : ℝ), (27837038699707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2305512561/5000000000 : ℝ)|^133 ≤ (9020235773337/25000000000000 : ℝ)^101
        have hw : |(2305512561/5000000000 : ℝ)|=(2305512561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2305564729/5000000000 : ℝ)|^133 ≤ (9020504546813/25000000000000 : ℝ)^101
        have hw : |(2305564729/5000000000 : ℝ)|=(2305564729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(946645937/2500000000 : ℝ)|^133 ≤ (27837038699707/100000000000000 : ℝ)^101
        have hw : |(946645937/2500000000 : ℝ)|=(946645937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-98008521/312500000 : ℝ)*x 0 + (1379821489/5000000000 : ℝ)*x 1 + (6778422083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98008521/312500000 : ℝ)^133 ≤ (21720096720331/100000000000000 : ℝ)^101 := by
    have hnat : (98008521 : ℕ)^133*100000000000000^101 ≤ 21720096720331^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98008521 312500000 21720096720331 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379821489/5000000000 : ℝ)^133 ≤ (18352590868981/100000000000000 : ℝ)^101 := by
    have hnat : (1379821489 : ℕ)^133*100000000000000^101 ≤ 18352590868981^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379821489 5000000000 18352590868981 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6778422083/10000000000 : ℝ)^133 ≤ (1498182809789/2500000000000 : ℝ)^101 := by
    have hnat : (6778422083 : ℕ)^133*2500000000000^101 ≤ 1498182809789^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6778422083 10000000000 1498182809789 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98008521/312500000 : ℝ), (1379821489/5000000000 : ℝ), (6778422083/10000000000 : ℝ)] ![(21720096720331/100000000000000 : ℝ), (18352590868981/100000000000000 : ℝ), (1498182809789/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98008521/312500000 : ℝ)|^133 ≤ (21720096720331/100000000000000 : ℝ)^101
        have hw : |(-98008521/312500000 : ℝ)|=(98008521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379821489/5000000000 : ℝ)|^133 ≤ (18352590868981/100000000000000 : ℝ)^101
        have hw : |(1379821489/5000000000 : ℝ)|=(1379821489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6778422083/10000000000 : ℝ)|^133 ≤ (1498182809789/2500000000000 : ℝ)^101
        have hw : |(6778422083/10000000000 : ℝ)|=(6778422083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3136185807/10000000000 : ℝ)*x 0 + (-551913309/2000000000 : ℝ)*x 1 + (3389273811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3136185807/10000000000 : ℝ)^133 ≤ (10859652272671/50000000000000 : ℝ)^101 := by
    have hnat : (3136185807 : ℕ)^133*50000000000000^101 ≤ 10859652272671^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136185807 10000000000 10859652272671 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551913309/2000000000 : ℝ)^133 ≤ (4587980379559/25000000000000 : ℝ)^101 := by
    have hnat : (551913309 : ℕ)^133*25000000000000^101 ≤ 4587980379559^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551913309 2000000000 4587980379559 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3389273811/5000000000 : ℝ)^133 ≤ (59928773917067/100000000000000 : ℝ)^101 := by
    have hnat : (3389273811 : ℕ)^133*100000000000000^101 ≤ 59928773917067^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389273811 5000000000 59928773917067 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3136185807/10000000000 : ℝ), (-551913309/2000000000 : ℝ), (3389273811/5000000000 : ℝ)] ![(10859652272671/50000000000000 : ℝ), (4587980379559/25000000000000 : ℝ), (59928773917067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3136185807/10000000000 : ℝ)|^133 ≤ (10859652272671/50000000000000 : ℝ)^101
        have hw : |(3136185807/10000000000 : ℝ)|=(3136185807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551913309/2000000000 : ℝ)|^133 ≤ (4587980379559/25000000000000 : ℝ)^101
        have hw : |(-551913309/2000000000 : ℝ)|=(551913309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3389273811/5000000000 : ℝ)|^133 ≤ (59928773917067/100000000000000 : ℝ)^101
        have hw : |(3389273811/5000000000 : ℝ)|=(3389273811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2598178333/5000000000 : ℝ)*x 0 + (818792613/1250000000 : ℝ)*x 1 + (-174399173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598178333/5000000000 : ℝ)^133 ≤ (42230222825613/100000000000000 : ℝ)^101 := by
    have hnat : (2598178333 : ℕ)^133*100000000000000^101 ≤ 42230222825613^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598178333 5000000000 42230222825613 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818792613/1250000000 : ℝ)^133 ≤ (28643131068849/50000000000000 : ℝ)^101 := by
    have hnat : (818792613 : ℕ)^133*50000000000000^101 ≤ 28643131068849^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818792613 1250000000 28643131068849 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174399173/10000000000 : ℝ)^133 ≤ (483515031949/100000000000000 : ℝ)^101 := by
    have hnat : (174399173 : ℕ)^133*100000000000000^101 ≤ 483515031949^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174399173 10000000000 483515031949 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598178333/5000000000 : ℝ), (818792613/1250000000 : ℝ), (-174399173/10000000000 : ℝ)] ![(42230222825613/100000000000000 : ℝ), (28643131068849/50000000000000 : ℝ), (483515031949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598178333/5000000000 : ℝ)|^133 ≤ (42230222825613/100000000000000 : ℝ)^101
        have hw : |(2598178333/5000000000 : ℝ)|=(2598178333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(818792613/1250000000 : ℝ)|^133 ≤ (28643131068849/50000000000000 : ℝ)^101
        have hw : |(818792613/1250000000 : ℝ)|=(818792613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174399173/10000000000 : ℝ)|^133 ≤ (483515031949/100000000000000 : ℝ)^101
        have hw : |(-174399173/10000000000 : ℝ)|=(174399173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2297265847/5000000000 : ℝ)*x 0 + (5791701923/10000000000 : ℝ)*x 1 + (1206235607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2297265847/5000000000 : ℝ)^133 ≤ (35911089309353/100000000000000 : ℝ)^101 := by
    have hnat : (2297265847 : ℕ)^133*100000000000000^101 ≤ 35911089309353^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297265847 5000000000 35911089309353 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5791701923/10000000000 : ℝ)^133 ≤ (48714213154477/100000000000000 : ℝ)^101 := by
    have hnat : (5791701923 : ℕ)^133*100000000000000^101 ≤ 48714213154477^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5791701923 10000000000 48714213154477 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206235607/5000000000 : ℝ)^133 ≤ (15374697523163/100000000000000 : ℝ)^101 := by
    have hnat : (1206235607 : ℕ)^133*100000000000000^101 ≤ 15374697523163^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206235607 5000000000 15374697523163 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2297265847/5000000000 : ℝ), (5791701923/10000000000 : ℝ), (1206235607/5000000000 : ℝ)] ![(35911089309353/100000000000000 : ℝ), (48714213154477/100000000000000 : ℝ), (15374697523163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2297265847/5000000000 : ℝ)|^133 ≤ (35911089309353/100000000000000 : ℝ)^101
        have hw : |(2297265847/5000000000 : ℝ)|=(2297265847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5791701923/10000000000 : ℝ)|^133 ≤ (48714213154477/100000000000000 : ℝ)^101
        have hw : |(5791701923/10000000000 : ℝ)|=(5791701923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206235607/5000000000 : ℝ)|^133 ≤ (15374697523163/100000000000000 : ℝ)^101
        have hw : |(1206235607/5000000000 : ℝ)|=(1206235607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2759731/10000000 : ℝ)*x 0 + (3136185727/10000000000 : ℝ)*x 1 + (3389211989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759731/10000000 : ℝ)^133 ≤ (4588340428991/25000000000000 : ℝ)^101 := by
    have hnat : (2759731 : ℕ)^133*25000000000000^101 ≤ 4588340428991^101*10000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759731 10000000 4588340428991 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3136185727/10000000000 : ℝ)^133 ≤ (678728244243/3125000000000 : ℝ)^101 := by
    have hnat : (3136185727 : ℕ)^133*3125000000000^101 ≤ 678728244243^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136185727 10000000000 678728244243 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3389211989/5000000000 : ℝ)^133 ≤ (29963667226547/50000000000000 : ℝ)^101 := by
    have hnat : (3389211989 : ℕ)^133*50000000000000^101 ≤ 29963667226547^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389211989 5000000000 29963667226547 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2759731/10000000 : ℝ), (3136185727/10000000000 : ℝ), (3389211989/5000000000 : ℝ)] ![(4588340428991/25000000000000 : ℝ), (678728244243/3125000000000 : ℝ), (29963667226547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2759731/10000000 : ℝ)|^133 ≤ (4588340428991/25000000000000 : ℝ)^101
        have hw : |(-2759731/10000000 : ℝ)|=(2759731/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3136185727/10000000000 : ℝ)|^133 ≤ (678728244243/3125000000000 : ℝ)^101
        have hw : |(3136185727/10000000000 : ℝ)|=(3136185727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3389211989/5000000000 : ℝ)|^133 ≤ (29963667226547/50000000000000 : ℝ)^101
        have hw : |(3389211989/5000000000 : ℝ)|=(3389211989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1379826671/5000000000 : ℝ)*x 0 + (-784024369/2500000000 : ℝ)*x 1 + (1694637881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379826671/5000000000 : ℝ)^133 ≤ (18352681630637/100000000000000 : ℝ)^101 := by
    have hnat : (1379826671 : ℕ)^133*100000000000000^101 ≤ 18352681630637^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379826671 5000000000 18352681630637 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784024369/2500000000 : ℝ)^133 ≤ (5429624752033/25000000000000 : ℝ)^101 := by
    have hnat : (784024369 : ℕ)^133*25000000000000^101 ≤ 5429624752033^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784024369 2500000000 5429624752033 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694637881/2500000000 : ℝ)^133 ≤ (59928819344303/100000000000000 : ℝ)^101 := by
    have hnat : (1694637881 : ℕ)^133*100000000000000^101 ≤ 59928819344303^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694637881 2500000000 59928819344303 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379826671/5000000000 : ℝ), (-784024369/2500000000 : ℝ), (1694637881/2500000000 : ℝ)] ![(18352681630637/100000000000000 : ℝ), (5429624752033/25000000000000 : ℝ), (59928819344303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379826671/5000000000 : ℝ)|^133 ≤ (18352681630637/100000000000000 : ℝ)^101
        have hw : |(1379826671/5000000000 : ℝ)|=(1379826671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-784024369/2500000000 : ℝ)|^133 ≤ (5429624752033/25000000000000 : ℝ)^101
        have hw : |(-784024369/2500000000 : ℝ)|=(784024369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1694637881/2500000000 : ℝ)|^133 ≤ (59928819344303/100000000000000 : ℝ)^101
        have hw : |(1694637881/2500000000 : ℝ)|=(1694637881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1310043263/2000000000 : ℝ)*x 0 + (1299122663/2500000000 : ℝ)*x 1 + (-2724991/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310043263/2000000000 : ℝ)^133 ≤ (57284827324901/100000000000000 : ℝ)^101 := by
    have hnat : (1310043263 : ℕ)^133*100000000000000^101 ≤ 57284827324901^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310043263 2000000000 57284827324901 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299122663/2500000000 : ℝ)^133 ≤ (4223165671577/10000000000000 : ℝ)^101 := by
    have hnat : (1299122663 : ℕ)^133*10000000000000^101 ≤ 4223165671577^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299122663 2500000000 4223165671577 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724991/156250000 : ℝ)^133 ≤ (120878987079/25000000000000 : ℝ)^101 := by
    have hnat : (2724991 : ℕ)^133*25000000000000^101 ≤ 120878987079^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724991 156250000 120878987079 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310043263/2000000000 : ℝ), (1299122663/2500000000 : ℝ), (-2724991/156250000 : ℝ)] ![(57284827324901/100000000000000 : ℝ), (4223165671577/10000000000000 : ℝ), (120878987079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310043263/2000000000 : ℝ)|^133 ≤ (57284827324901/100000000000000 : ℝ)^101
        have hw : |(1310043263/2000000000 : ℝ)|=(1310043263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299122663/2500000000 : ℝ)|^133 ≤ (4223165671577/10000000000000 : ℝ)^101
        have hw : |(1299122663/2500000000 : ℝ)|=(1299122663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2724991/156250000 : ℝ)|^133 ≤ (120878987079/25000000000000 : ℝ)^101
        have hw : |(-2724991/156250000 : ℝ)|=(2724991/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_18 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5791590979/10000000000 : ℝ)*x 0 + (4594649541/10000000000 : ℝ)*x 1 + (482494621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5791590979/10000000000 : ℝ)^133 ≤ (190285095123/390625000000 : ℝ)^101 := by
    have hnat : (5791590979 : ℕ)^133*390625000000^101 ≤ 190285095123^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5791590979 10000000000 190285095123 390625000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4594649541/10000000000 : ℝ)^133 ≤ (8978075561341/25000000000000 : ℝ)^101 := by
    have hnat : (4594649541 : ℕ)^133*25000000000000^101 ≤ 8978075561341^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594649541 10000000000 8978075561341 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482494621/2000000000 : ℝ)^133 ≤ (7687356696387/50000000000000 : ℝ)^101 := by
    have hnat : (482494621 : ℕ)^133*50000000000000^101 ≤ 7687356696387^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482494621 2000000000 7687356696387 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5791590979/10000000000 : ℝ), (4594649541/10000000000 : ℝ), (482494621/2000000000 : ℝ)] ![(190285095123/390625000000 : ℝ), (8978075561341/25000000000000 : ℝ), (7687356696387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5791590979/10000000000 : ℝ)|^133 ≤ (190285095123/390625000000 : ℝ)^101
        have hw : |(5791590979/10000000000 : ℝ)|=(5791590979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4594649541/10000000000 : ℝ)|^133 ≤ (8978075561341/25000000000000 : ℝ)^101
        have hw : |(4594649541/10000000000 : ℝ)|=(4594649541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(482494621/2000000000 : ℝ)|^133 ≤ (7687356696387/50000000000000 : ℝ)^101
        have hw : |(482494621/2000000000 : ℝ)|=(482494621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3948037763/10000000000 : ℝ)*x 0 + (1459568467/5000000000 : ℝ)*x 1 + (2990764327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3948037763/10000000000 : ℝ)^133 ≤ (14705239755787/50000000000000 : ℝ)^101 := by
    have hnat : (3948037763 : ℕ)^133*50000000000000^101 ≤ 14705239755787^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948037763 10000000000 14705239755787 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459568467/5000000000 : ℝ)^133 ≤ (19761965682479/100000000000000 : ℝ)^101 := by
    have hnat : (1459568467 : ℕ)^133*100000000000000^101 ≤ 19761965682479^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459568467 5000000000 19761965682479 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2990764327/5000000000 : ℝ)^133 ≤ (50827554796363/100000000000000 : ℝ)^101 := by
    have hnat : (2990764327 : ℕ)^133*100000000000000^101 ≤ 50827554796363^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990764327 5000000000 50827554796363 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3948037763/10000000000 : ℝ), (1459568467/5000000000 : ℝ), (2990764327/5000000000 : ℝ)] ![(14705239755787/50000000000000 : ℝ), (19761965682479/100000000000000 : ℝ), (50827554796363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3948037763/10000000000 : ℝ)|^133 ≤ (14705239755787/50000000000000 : ℝ)^101
        have hw : |(-3948037763/10000000000 : ℝ)|=(3948037763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1459568467/5000000000 : ℝ)|^133 ≤ (19761965682479/100000000000000 : ℝ)^101
        have hw : |(1459568467/5000000000 : ℝ)|=(1459568467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2990764327/5000000000 : ℝ)|^133 ≤ (50827554796363/100000000000000 : ℝ)^101
        have hw : |(2990764327/5000000000 : ℝ)|=(2990764327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2919156779/10000000000 : ℝ)*x 0 + (-3947874187/10000000000 : ℝ)*x 1 + (5981656243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2919156779/10000000000 : ℝ)^133 ≤ (2470267824321/12500000000000 : ℝ)^101 := by
    have hnat : (2919156779 : ℕ)^133*12500000000000^101 ≤ 2470267824321^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919156779 10000000000 2470267824321 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3947874187/10000000000 : ℝ)^133 ≤ (5881774981561/20000000000000 : ℝ)^101 := by
    have hnat : (3947874187 : ℕ)^133*20000000000000^101 ≤ 5881774981561^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3947874187 10000000000 5881774981561 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5981656243/10000000000 : ℝ)^133 ≤ (50828982480053/100000000000000 : ℝ)^101 := by
    have hnat : (5981656243 : ℕ)^133*100000000000000^101 ≤ 50828982480053^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5981656243 10000000000 50828982480053 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2919156779/10000000000 : ℝ), (-3947874187/10000000000 : ℝ), (5981656243/10000000000 : ℝ)] ![(2470267824321/12500000000000 : ℝ), (5881774981561/20000000000000 : ℝ), (50828982480053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2919156779/10000000000 : ℝ)|^133 ≤ (2470267824321/12500000000000 : ℝ)^101
        have hw : |(2919156779/10000000000 : ℝ)|=(2919156779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3947874187/10000000000 : ℝ)|^133 ≤ (5881774981561/20000000000000 : ℝ)^101
        have hw : |(-3947874187/10000000000 : ℝ)|=(3947874187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5981656243/10000000000 : ℝ)|^133 ≤ (50828982480053/100000000000000 : ℝ)^101
        have hw : |(5981656243/10000000000 : ℝ)|=(5981656243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3026310159/5000000000 : ℝ)*x 0 + (681261583/1250000000 : ℝ)*x 1 + (-96071201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3026310159/5000000000 : ℝ)^133 ≤ (6453067601501/12500000000000 : ℝ)^101 := by
    have hnat : (3026310159 : ℕ)^133*12500000000000^101 ≤ 6453067601501^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3026310159 5000000000 6453067601501 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681261583/1250000000 : ℝ)^133 ≤ (1798656689681/4000000000000 : ℝ)^101 := by
    have hnat : (681261583 : ℕ)^133*4000000000000^101 ≤ 1798656689681^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681261583 1250000000 1798656689681 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96071201/1250000000 : ℝ)^133 ≤ (3409041920879/100000000000000 : ℝ)^101 := by
    have hnat : (96071201 : ℕ)^133*100000000000000^101 ≤ 3409041920879^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96071201 1250000000 3409041920879 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3026310159/5000000000 : ℝ), (681261583/1250000000 : ℝ), (-96071201/1250000000 : ℝ)] ![(6453067601501/12500000000000 : ℝ), (1798656689681/4000000000000 : ℝ), (3409041920879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3026310159/5000000000 : ℝ)|^133 ≤ (6453067601501/12500000000000 : ℝ)^101
        have hw : |(3026310159/5000000000 : ℝ)|=(3026310159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681261583/1250000000 : ℝ)|^133 ≤ (1798656689681/4000000000000 : ℝ)^101
        have hw : |(681261583/1250000000 : ℝ)|=(681261583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96071201/1250000000 : ℝ)|^133 ≤ (3409041920879/100000000000000 : ℝ)^101
        have hw : |(-96071201/1250000000 : ℝ)|=(96071201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304057_s4_s4_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2031365653/5000000000 : ℝ)*x 0 + (5288308549/10000000000 : ℝ)*x 1 + (1810341283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031365653/5000000000 : ℝ)^133 ≤ (15270360340419/50000000000000 : ℝ)^101 := by
    have hnat : (2031365653 : ℕ)^133*50000000000000^101 ≤ 15270360340419^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031365653 5000000000 15270360340419 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5288308549/10000000000 : ℝ)^133 ≤ (43217016114799/100000000000000 : ℝ)^101 := by
    have hnat : (5288308549 : ℕ)^133*100000000000000^101 ≤ 43217016114799^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288308549 10000000000 43217016114799 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1810341283/5000000000 : ℝ)^133 ≤ (13121131592743/50000000000000 : ℝ)^101 := by
    have hnat : (1810341283 : ℕ)^133*50000000000000^101 ≤ 13121131592743^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810341283 5000000000 13121131592743 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031365653/5000000000 : ℝ), (5288308549/10000000000 : ℝ), (1810341283/5000000000 : ℝ)] ![(15270360340419/50000000000000 : ℝ), (43217016114799/100000000000000 : ℝ), (13121131592743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031365653/5000000000 : ℝ)|^133 ≤ (15270360340419/50000000000000 : ℝ)^101
        have hw : |(2031365653/5000000000 : ℝ)|=(2031365653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5288308549/10000000000 : ℝ)|^133 ≤ (43217016114799/100000000000000 : ℝ)^101
        have hw : |(5288308549/10000000000 : ℝ)|=(5288308549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1810341283/5000000000 : ℝ)|^133 ≤ (13121131592743/50000000000000 : ℝ)^101
        have hw : |(1810341283/5000000000 : ℝ)|=(1810341283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304057_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((2249/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2249/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1799/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1799/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16719/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22063/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22063/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3999/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3999/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (2249/3125 : ℝ) ^ (33/8 : ℝ) ≤ (25745430855676134083/100000000000000000000 : ℝ) := by
    have hpowers : (2249/3125 : ℝ)^33 ≤ (25745430855676134083/100000000000000000000 : ℝ)^8 := by
      have hnat : (2249 : ℕ)^33*100000000000000000000^8 ≤ 25745430855676134083^8*3125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 3125 25745430855676134083 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/3125 : ℝ)) (X := (25745430855676134083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (125745430855676134083/100000000000000000000 : ℝ) ≤ (330346223326463/312500000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (125745430855676134083/100000000000000000000 : ℝ)^8 ≤ (330346223326463/312500000000000 : ℝ)^33 := by
      have hnat : (125745430855676134083 : ℕ)^8*312500000000000^33 ≤ 330346223326463^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125745430855676134083 100000000000000000000 330346223326463 312500000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (330346223326463/312500000000000 : ℝ)) (X := (125745430855676134083/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (75745430855676134083/50000000000000000000 : ℝ) ≤ (5529680634116169/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (75745430855676134083/50000000000000000000 : ℝ)^8 ≤ (5529680634116169/5000000000000000 : ℝ)^33 := by
      have hnat : (75745430855676134083 : ℕ)^8*5000000000000000^33 ≤ 5529680634116169^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75745430855676134083 50000000000000000000 5529680634116169 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5529680634116169/5000000000000000 : ℝ)) (X := (75745430855676134083/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(17846223326463/224900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(244141060892761/3598400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (2249/3125 : ℝ)) (alpha := (17846223326463/224900000000000 : ℝ)) (beta := (244141060892761/3598400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2249/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(17846223326463/224900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(244141060892761/3598400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (1799/2500 : ℝ) ^ (33/8 : ℝ) ≤ (3216703458754051937/12500000000000000000 : ℝ) := by
    have hpowers : (1799/2500 : ℝ)^33 ≤ (3216703458754051937/12500000000000000000 : ℝ)^8 := by
      have hnat : (1799 : ℕ)^33*12500000000000000000^8 ≤ 3216703458754051937^8*2500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1799 2500 3216703458754051937 12500000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1799/2500 : ℝ)) (X := (3216703458754051937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (15716703458754051937/12500000000000000000 : ℝ) ≤ (422833543581437/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (15716703458754051937/12500000000000000000 : ℝ)^8 ≤ (422833543581437/400000000000000 : ℝ)^33 := by
      have hnat : (15716703458754051937 : ℕ)^8*400000000000000^33 ≤ 422833543581437^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15716703458754051937 12500000000000000000 422833543581437 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (422833543581437/400000000000000 : ℝ)) (X := (15716703458754051937/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (9466703458754051937/6250000000000000000 : ℝ) ≤ (5529471731186737/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (9466703458754051937/6250000000000000000 : ℝ)^8 ≤ (5529471731186737/5000000000000000 : ℝ)^33 := by
      have hnat : (9466703458754051937 : ℕ)^8*5000000000000000^33 ≤ 5529471731186737^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9466703458754051937 6250000000000000000 5529471731186737 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5529471731186737/5000000000000000 : ℝ)) (X := (9466703458754051937/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(22833543581437/287840000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(488104872837549/7196000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1799/2500 : ℝ)) (alpha := (22833543581437/287840000000000 : ℝ)) (beta := (488104872837549/7196000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1799/2500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(22833543581437/287840000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(488104872837549/7196000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (16719/100000 : ℝ) ^ (33/8 : ℝ) ≤ (62480209678039469/100000000000000000000 : ℝ) := by
    have hpowers : (16719/100000 : ℝ)^33 ≤ (62480209678039469/100000000000000000000 : ℝ)^8 := by
      have hnat : (16719 : ℕ)^33*100000000000000000000^8 ≤ 62480209678039469^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16719 100000 62480209678039469 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16719/100000 : ℝ)) (X := (62480209678039469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (100062480209678039469/100000000000000000000 : ℝ) ≤ (2000302862681483/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100062480209678039469/100000000000000000000 : ℝ)^8 ≤ (2000302862681483/2000000000000000 : ℝ)^33 := by
      have hnat : (100062480209678039469 : ℕ)^8*2000000000000000^33 ≤ 2000302862681483^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062480209678039469 100000000000000000000 2000302862681483 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000302862681483/2000000000000000 : ℝ)) (X := (100062480209678039469/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (50062480209678039469/50000000000000000000 : ℝ) ≤ (10003027910654311/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50062480209678039469/50000000000000000000 : ℝ)^8 ≤ (10003027910654311/10000000000000000 : ℝ)^33 := by
      have hnat : (50062480209678039469 : ℕ)^8*10000000000000000^33 ≤ 10003027910654311^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062480209678039469 50000000000000000000 10003027910654311 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003027910654311/10000000000000000 : ℝ)) (X := (50062480209678039469/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(100954227161/111460000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(31533275977/34831250000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (16719/100000 : ℝ)) (alpha := (100954227161/111460000000000 : ℝ)) (beta := (31533275977/34831250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16719/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(100954227161/111460000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(31533275977/34831250000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-106389299/312500000 : ℝ)*X 0 0+(170218297/500000000 : ℝ)*X 0 1+(1512701039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((3404379297/10000000000 : ℝ)*X 1 0+(-3404287671/10000000000 : ℝ)*X 1 1+(6050934619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((2305512561/5000000000 : ℝ)*X 0 0+(2305564729/5000000000 : ℝ)*X 0 1+(946645937/2500000000 : ℝ)*X 0 2+(2305512561/5000000000 : ℝ)*X 1 0+(2305564729/5000000000 : ℝ)*X 1 1+(946645937/2500000000 : ℝ)*X 1 2+(2305512561/5000000000 : ℝ)*X 2 0+(2305564729/5000000000 : ℝ)*X 2 1+(946645937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-98008521/312500000 : ℝ)*X 0 0+(1379821489/5000000000 : ℝ)*X 0 1+(6778422083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((3136185807/10000000000 : ℝ)*X 1 0+(-551913309/2000000000 : ℝ)*X 1 1+(3389273811/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2598178333/5000000000 : ℝ)*X 2 0+(818792613/1250000000 : ℝ)*X 2 1+(-174399173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_12 : ((2297265847/5000000000 : ℝ)*X 0 0+(5791701923/10000000000 : ℝ)*X 0 1+(1206235607/5000000000 : ℝ)*X 0 2+(2297265847/5000000000 : ℝ)*X 1 0+(5791701923/10000000000 : ℝ)*X 1 1+(1206235607/5000000000 : ℝ)*X 1 2+(2297265847/5000000000 : ℝ)*X 2 0+(5791701923/10000000000 : ℝ)*X 2 1+(1206235607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((-2759731/10000000 : ℝ)*X 0 0+(3136185727/10000000000 : ℝ)*X 0 1+(3389211989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((1379826671/5000000000 : ℝ)*X 1 0+(-784024369/2500000000 : ℝ)*X 1 1+(1694637881/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((1310043263/2000000000 : ℝ)*X 2 0+(1299122663/2500000000 : ℝ)*X 2 1+(-2724991/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_18 : ((5791590979/10000000000 : ℝ)*X 0 0+(4594649541/10000000000 : ℝ)*X 0 1+(482494621/2000000000 : ℝ)*X 0 2+(5791590979/10000000000 : ℝ)*X 1 0+(4594649541/10000000000 : ℝ)*X 1 1+(482494621/2000000000 : ℝ)*X 1 2+(5791590979/10000000000 : ℝ)*X 2 0+(4594649541/10000000000 : ℝ)*X 2 1+(482494621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_19 : ((-3948037763/10000000000 : ℝ)*X 0 0+(1459568467/5000000000 : ℝ)*X 0 1+(2990764327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((2919156779/10000000000 : ℝ)*X 1 0+(-3947874187/10000000000 : ℝ)*X 1 1+(5981656243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((3026310159/5000000000 : ℝ)*X 2 0+(681261583/1250000000 : ℝ)*X 2 1+(-96071201/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_25 : ((2031365653/5000000000 : ℝ)*X 0 0+(5288308549/10000000000 : ℝ)*X 0 1+(1810341283/5000000000 : ℝ)*X 0 2+(2031365653/5000000000 : ℝ)*X 1 0+(5288308549/10000000000 : ℝ)*X 1 1+(1810341283/5000000000 : ℝ)*X 1 2+(2031365653/5000000000 : ℝ)*X 2 0+(5288308549/10000000000 : ℝ)*X 2 1+(1810341283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304057_s4_s4_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((44127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (86230299051526581455060865093/11274042461500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4037/200000000000 : ℝ)*(base23) + (842141/250000000000 : ℝ)*(base39) + (2398321/500000000000 : ℝ)*(base49) + (490575588463/200000000000 : ℝ)*(base59) + (1084525116463/1000000000000 : ℝ)*(base60) + (691765692031/125000000000 : ℝ)*(major_s4_0) + (691765692031/125000000000 : ℝ)*(major_s4_1) + (691765692031/125000000000 : ℝ)*(major_s4_2) + (1483881723051/200000000000 : ℝ)*(sp_s4_7) + (3709751425281/500000000000 : ℝ)*(sp_s4_8) + (3709751415189/500000000000 : ℝ)*(sp_s4_9) + (228042140593/62500000000 : ℝ)*(sp_s4_12) + (23558827/250000000000 : ℝ)*(sp_s4_13) + (17855729/250000000000 : ℝ)*(sp_s4_25) + (912186418101/250000000000 : ℝ)*(f.failure) + (3709751425281/500000000000 : ℝ)*(f.sum) + (53359083317885673/200516540000000000000000000000 : ℝ)*base62 + (40269695751739/139325000000000000000000000 : ℝ)*base64 + (946183857444131/899500000000000000000000000 : ℝ)*base66 + (2221688535561/5573000000000000000000000 : ℝ)*base68 + (38367931149456743/313341925000000000000000000000 : ℝ)*base70 + (50163561363369/449800000000000000000000000 : ℝ)*base72 + (19169328387621/35980000000000000000000000 : ℝ)*base74 + (148317927499/219628906250000000000000 : ℝ)*base76 + (2991125488997056893/4045951000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1859/3125000000000000 : ℝ)*base87 + (1859/3125000000000000 : ℝ)*base89 + (1859/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22063/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22063/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (879617540694761873215891587/128846199560000000000000000000000 : ℝ) := by norm_num
    linear_combination (7651141/1000000000000 : ℝ)*(base21) + (1226426083461/500000000000 : ℝ)*(base59) + (273674408977/200000000000 : ℝ)*(base60) + (55340873707/10000000000 : ℝ)*(major_s4_0) + (55340873707/10000000000 : ℝ)*(major_s4_1) + (55340873707/10000000000 : ℝ)*(major_s4_2) + (209611/250000000000 : ℝ)*(sp_s4_1) + (11288327/1000000000000 : ℝ)*(sp_s4_6) + (38782483/500000000000 : ℝ)*(sp_s4_8) + (296778078263/40000000000 : ℝ)*(sp_s4_13) + (1854843388291/250000000000 : ℝ)*(sp_s4_14) + (3709707687123/500000000000 : ℝ)*(sp_s4_15) + (3648709220863/1000000000000 : ℝ)*(sp_s4_18) + (7232797/250000000000 : ℝ)*(sp_s4_21) + (3648720509191/1000000000000 : ℝ)*(f.failure) + (296778078263/40000000000 : ℝ)*(f.sum) + (43099722885606801/57290440000000000000000000000 : ℝ)*base63 + (5134986485279/27865000000000000000000000 : ℝ)*base65 + (3998921914741/10280000000000000000000000 : ℝ)*base67 + (66086931675053/55730000000000000000000000 : ℝ)*base69 + (32112275168320137/125336770000000000000000000000 : ℝ)*base70 + (37641778808763/35984000000000000000000000 : ℝ)*base73 + (967683528233/2056000000000000000000000 : ℝ)*base75 + (14758933333033/22490000000000000000000000 : ℝ)*base77 + (2078786064053013/9247888000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2169/12500000000000000 : ℝ)*base87 + (2169/12500000000000000 : ℝ)*base89 + (2169/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3999/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3999/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1110289683331501205336625224679/90192339692000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2827001/1000000000000 : ℝ)*(base40) + (2876341/1000000000000 : ℝ)*(base50) + (381127012057/500000000000 : ℝ)*(base59) + (2942354109883/1000000000000 : ℝ)*(major_s4_0) + (2942354109883/1000000000000 : ℝ)*(major_s4_1) + (2942354109883/1000000000000 : ℝ)*(major_s4_2) + (137/25000000000 : ℝ)*(sp_s4_0) + (9501513/500000000000 : ℝ)*(sp_s4_9) + (84154403/1000000000000 : ℝ)*(sp_s4_12) + (3170859/62500000000 : ℝ)*(sp_s4_15) + (788951725981/200000000000 : ℝ)*(sp_s4_19) + (788951727077/200000000000 : ℝ)*(sp_s4_20) + (1972344449307/500000000000 : ℝ)*(sp_s4_21) + (969930663279/500000000000 : ℝ)*(sp_s4_25) + (1939945480961/1000000000000 : ℝ)*(f.failure) + (788951727077/200000000000 : ℝ)*(f.sum) + (817714628828282387/1604132320000000000000000000000 : ℝ)*base63 + (169789113603093/278650000000000000000000000 : ℝ)*base64 + (5553075909675233/7196000000000000000000000000 : ℝ)*base66 + (30183224685533/111460000000000000000000000 : ℝ)*base68 + (342103360839355247/1253367700000000000000000000000 : ℝ)*base70 + (1274691399483037/3598400000000000000000000000 : ℝ)*base72 + (204320941409199/287840000000000000000000000 : ℝ)*base75 + (57301526412319/224900000000000000000000000 : ℝ)*base77 + (16351849459339043049/32367608000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2099/12500000000000000 : ℝ)*base87 + (2099/12500000000000000 : ℝ)*base89 + (2099/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((2249/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2249/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1799/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1799/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16719/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16719/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44127/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44127/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22063/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22063/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3999/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3999/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304057_s4 p hpa hpb X hX hprev3

#print axioms solution
