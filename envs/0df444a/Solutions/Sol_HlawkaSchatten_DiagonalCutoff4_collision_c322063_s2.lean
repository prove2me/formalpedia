-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:48:00.957982+00:00
-- url     : https://prove2.me/submissions/38bfcacd-3c08-4bfc-a43c-8a7770457624

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
theorem collision_support_c322063_s2_s2_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-666668913/5000000000 : ℝ)*x 0 + (1331454767/2500000000 : ℝ)*x 1 + (5337181099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666668913/5000000000 : ℝ)^83 ≤ (8240825072103/100000000000000 : ℝ)^67 := by
    have hnat : (666668913 : ℕ)^83*100000000000000^67 ≤ 8240825072103^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666668913 5000000000 8240825072103 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331454767/2500000000 : ℝ)^83 ≤ (45819025587453/100000000000000 : ℝ)^67 := by
    have hnat : (1331454767 : ℕ)^83*100000000000000^67 ≤ 45819025587453^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331454767 2500000000 45819025587453 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5337181099/10000000000 : ℝ)^83 ≤ (11485037330687/25000000000000 : ℝ)^67 := by
    have hnat : (5337181099 : ℕ)^83*25000000000000^67 ≤ 11485037330687^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337181099 10000000000 11485037330687 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-666668913/5000000000 : ℝ), (1331454767/2500000000 : ℝ), (5337181099/10000000000 : ℝ)] ![(8240825072103/100000000000000 : ℝ), (45819025587453/100000000000000 : ℝ), (11485037330687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-666668913/5000000000 : ℝ)|^83 ≤ (8240825072103/100000000000000 : ℝ)^67
        have hw : |(-666668913/5000000000 : ℝ)|=(666668913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1331454767/2500000000 : ℝ)|^83 ≤ (45819025587453/100000000000000 : ℝ)^67
        have hw : |(1331454767/2500000000 : ℝ)|=(1331454767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5337181099/10000000000 : ℝ)|^83 ≤ (11485037330687/25000000000000 : ℝ)^67
        have hw : |(5337181099/10000000000 : ℝ)|=(5337181099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5326276449/10000000000 : ℝ)*x 0 + (-267390689/2000000000 : ℝ)*x 1 + (533412673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5326276449/10000000000 : ℝ)^83 ≤ (45823900258381/100000000000000 : ℝ)^67 := by
    have hnat : (5326276449 : ℕ)^83*100000000000000^67 ≤ 45823900258381^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5326276449 10000000000 45823900258381 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267390689/2000000000 : ℝ)^83 ≤ (8268517239237/100000000000000 : ℝ)^67 := by
    have hnat : (267390689 : ℕ)^83*100000000000000^67 ≤ 8268517239237^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267390689 2000000000 8268517239237 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533412673/1000000000 : ℝ)^83 ≤ (45907582486199/100000000000000 : ℝ)^67 := by
    have hnat : (533412673 : ℕ)^83*100000000000000^67 ≤ 45907582486199^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533412673 1000000000 45907582486199 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5326276449/10000000000 : ℝ), (-267390689/2000000000 : ℝ), (533412673/1000000000 : ℝ)] ![(45823900258381/100000000000000 : ℝ), (8268517239237/100000000000000 : ℝ), (45907582486199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5326276449/10000000000 : ℝ)|^83 ≤ (45823900258381/100000000000000 : ℝ)^67
        have hw : |(5326276449/10000000000 : ℝ)|=(5326276449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267390689/2000000000 : ℝ)|^83 ≤ (8268517239237/100000000000000 : ℝ)^67
        have hw : |(-267390689/2000000000 : ℝ)|=(267390689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(533412673/1000000000 : ℝ)|^83 ≤ (45907582486199/100000000000000 : ℝ)^67
        have hw : |(533412673/1000000000 : ℝ)|=(533412673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5335318933/10000000000 : ℝ)*x 0 + (106654163/200000000 : ℝ)*x 1 + (-66316793/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5335318933/10000000000 : ℝ)^83 ≤ (9184058735079/20000000000000 : ℝ)^67 := by
    have hnat : (5335318933 : ℕ)^83*20000000000000^67 ≤ 9184058735079^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5335318933 10000000000 9184058735079 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106654163/200000000 : ℝ)^83 ≤ (4589245856437/10000000000000 : ℝ)^67 := by
    have hnat : (106654163 : ℕ)^83*10000000000000^67 ≤ 4589245856437^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106654163 200000000 4589245856437 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66316793/500000000 : ℝ)^83 ≤ (4093623874343/50000000000000 : ℝ)^67 := by
    have hnat : (66316793 : ℕ)^83*50000000000000^67 ≤ 4093623874343^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66316793 500000000 4093623874343 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5335318933/10000000000 : ℝ), (106654163/200000000 : ℝ), (-66316793/500000000 : ℝ)] ![(9184058735079/20000000000000 : ℝ), (4589245856437/10000000000000 : ℝ), (4093623874343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5335318933/10000000000 : ℝ)|^83 ≤ (9184058735079/20000000000000 : ℝ)^67
        have hw : |(5335318933/10000000000 : ℝ)|=(5335318933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(106654163/200000000 : ℝ)|^83 ≤ (4589245856437/10000000000000 : ℝ)^67
        have hw : |(106654163/200000000 : ℝ)|=(106654163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66316793/500000000 : ℝ)|^83 ≤ (4093623874343/50000000000000 : ℝ)^67
        have hw : |(-66316793/500000000 : ℝ)|=(66316793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1030677851/2500000000 : ℝ)*x 0 + (515142043/1250000000 : ℝ)*x 1 + (4114919321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030677851/2500000000 : ℝ)^83 ≤ (16682315341813/50000000000000 : ℝ)^67 := by
    have hnat : (1030677851 : ℕ)^83*50000000000000^67 ≤ 16682315341813^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030677851 2500000000 16682315341813 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515142043/1250000000 : ℝ)^83 ≤ (8337210154221/25000000000000 : ℝ)^67 := by
    have hnat : (515142043 : ℕ)^83*25000000000000^67 ≤ 8337210154221^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515142043 1250000000 8337210154221 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114919321/10000000000 : ℝ)^83 ≤ (16643264339683/50000000000000 : ℝ)^67 := by
    have hnat : (4114919321 : ℕ)^83*50000000000000^67 ≤ 16643264339683^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114919321 10000000000 16643264339683 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030677851/2500000000 : ℝ), (515142043/1250000000 : ℝ), (4114919321/10000000000 : ℝ)] ![(16682315341813/50000000000000 : ℝ), (8337210154221/25000000000000 : ℝ), (16643264339683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030677851/2500000000 : ℝ)|^83 ≤ (16682315341813/50000000000000 : ℝ)^67
        have hw : |(1030677851/2500000000 : ℝ)|=(1030677851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515142043/1250000000 : ℝ)|^83 ≤ (8337210154221/25000000000000 : ℝ)^67
        have hw : |(515142043/1250000000 : ℝ)|=(515142043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114919321/10000000000 : ℝ)|^83 ≤ (16643264339683/50000000000000 : ℝ)^67
        have hw : |(4114919321/10000000000 : ℝ)|=(4114919321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-634209869/5000000000 : ℝ)*x 0 + (2369179071/5000000000 : ℝ)*x 1 + (297721803/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (634209869/5000000000 : ℝ)^83 ≤ (968337728523/12500000000000 : ℝ)^67 := by
    have hnat : (634209869 : ℕ)^83*12500000000000^67 ≤ 968337728523^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634209869 5000000000 968337728523 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2369179071/5000000000 : ℝ)^83 ≤ (39642942733077/100000000000000 : ℝ)^67 := by
    have hnat : (2369179071 : ℕ)^83*100000000000000^67 ≤ 39642942733077^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369179071 5000000000 39642942733077 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297721803/500000000 : ℝ)^83 ≤ (26305177707691/50000000000000 : ℝ)^67 := by
    have hnat : (297721803 : ℕ)^83*50000000000000^67 ≤ 26305177707691^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297721803 500000000 26305177707691 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-634209869/5000000000 : ℝ), (2369179071/5000000000 : ℝ), (297721803/500000000 : ℝ)] ![(968337728523/12500000000000 : ℝ), (39642942733077/100000000000000 : ℝ), (26305177707691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-634209869/5000000000 : ℝ)|^83 ≤ (968337728523/12500000000000 : ℝ)^67
        have hw : |(-634209869/5000000000 : ℝ)|=(634209869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2369179071/5000000000 : ℝ)|^83 ≤ (39642942733077/100000000000000 : ℝ)^67
        have hw : |(2369179071/5000000000 : ℝ)|=(2369179071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297721803/500000000 : ℝ)|^83 ≤ (26305177707691/50000000000000 : ℝ)^67
        have hw : |(297721803/500000000 : ℝ)|=(297721803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1018074817/2000000000 : ℝ)*x 0 + (-758941281/10000000000 : ℝ)*x 1 + (2975683617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018074817/2000000000 : ℝ)^83 ≤ (21661562545117/50000000000000 : ℝ)^67 := by
    have hnat : (1018074817 : ℕ)^83*50000000000000^67 ≤ 21661562545117^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018074817 2000000000 21661562545117 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758941281/10000000000 : ℝ)^83 ≤ (4100107118013/100000000000000 : ℝ)^67 := by
    have hnat : (758941281 : ℕ)^83*100000000000000^67 ≤ 4100107118013^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758941281 10000000000 4100107118013 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2975683617/5000000000 : ℝ)^83 ≤ (52576767780447/100000000000000 : ℝ)^67 := by
    have hnat : (2975683617 : ℕ)^83*100000000000000^67 ≤ 52576767780447^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975683617 5000000000 52576767780447 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1018074817/2000000000 : ℝ), (-758941281/10000000000 : ℝ), (2975683617/5000000000 : ℝ)] ![(21661562545117/50000000000000 : ℝ), (4100107118013/100000000000000 : ℝ), (52576767780447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1018074817/2000000000 : ℝ)|^83 ≤ (21661562545117/50000000000000 : ℝ)^67
        have hw : |(1018074817/2000000000 : ℝ)|=(1018074817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-758941281/10000000000 : ℝ)|^83 ≤ (4100107118013/100000000000000 : ℝ)^67
        have hw : |(-758941281/10000000000 : ℝ)|=(758941281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2975683617/5000000000 : ℝ)|^83 ≤ (52576767780447/100000000000000 : ℝ)^67
        have hw : |(2975683617/5000000000 : ℝ)|=(2975683617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2454232609/5000000000 : ℝ)*x 0 + (3067598107/5000000000 : ℝ)*x 1 + (-742528093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2454232609/5000000000 : ℝ)^83 ≤ (10353369621879/25000000000000 : ℝ)^67 := by
    have hnat : (2454232609 : ℕ)^83*25000000000000^67 ≤ 10353369621879^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454232609 5000000000 10353369621879 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3067598107/5000000000 : ℝ)^83 ≤ (54595974913637/100000000000000 : ℝ)^67 := by
    have hnat : (3067598107 : ℕ)^83*100000000000000^67 ≤ 54595974913637^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3067598107 5000000000 54595974913637 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742528093/10000000000 : ℝ)^83 ≤ (3990546589173/100000000000000 : ℝ)^67 := by
    have hnat : (742528093 : ℕ)^83*100000000000000^67 ≤ 3990546589173^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742528093 10000000000 3990546589173 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2454232609/5000000000 : ℝ), (3067598107/5000000000 : ℝ), (-742528093/10000000000 : ℝ)] ![(10353369621879/25000000000000 : ℝ), (54595974913637/100000000000000 : ℝ), (3990546589173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2454232609/5000000000 : ℝ)|^83 ≤ (10353369621879/25000000000000 : ℝ)^67
        have hw : |(2454232609/5000000000 : ℝ)|=(2454232609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3067598107/5000000000 : ℝ)|^83 ≤ (54595974913637/100000000000000 : ℝ)^67
        have hw : |(3067598107/5000000000 : ℝ)|=(3067598107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-742528093/10000000000 : ℝ)|^83 ≤ (3990546589173/100000000000000 : ℝ)^67
        have hw : |(-742528093/10000000000 : ℝ)|=(742528093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (139504439/312500000 : ℝ)*x 0 + (5331385789/10000000000 : ℝ)*x 1 + (2426305897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139504439/312500000 : ℝ)^83 ≤ (36820810998971/100000000000000 : ℝ)^67 := by
    have hnat : (139504439 : ℕ)^83*100000000000000^67 ≤ 36820810998971^67*312500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139504439 312500000 36820810998971 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5331385789/10000000000 : ℝ)^83 ≤ (22939180664183/50000000000000 : ℝ)^67 := by
    have hnat : (5331385789 : ℕ)^83*50000000000000^67 ≤ 22939180664183^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331385789 10000000000 22939180664183 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426305897/10000000000 : ℝ)^83 ≤ (17300827661227/100000000000000 : ℝ)^67 := by
    have hnat : (2426305897 : ℕ)^83*100000000000000^67 ≤ 17300827661227^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426305897 10000000000 17300827661227 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139504439/312500000 : ℝ), (5331385789/10000000000 : ℝ), (2426305897/10000000000 : ℝ)] ![(36820810998971/100000000000000 : ℝ), (22939180664183/50000000000000 : ℝ), (17300827661227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139504439/312500000 : ℝ)|^83 ≤ (36820810998971/100000000000000 : ℝ)^67
        have hw : |(139504439/312500000 : ℝ)|=(139504439/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5331385789/10000000000 : ℝ)|^83 ≤ (22939180664183/50000000000000 : ℝ)^67
        have hw : |(5331385789/10000000000 : ℝ)|=(5331385789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426305897/10000000000 : ℝ)|^83 ≤ (17300827661227/100000000000000 : ℝ)^67
        have hw : |(2426305897/10000000000 : ℝ)|=(2426305897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-760425373/10000000000 : ℝ)*x 0 + (5097188317/10000000000 : ℝ)*x 1 + (5943892677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760425373/10000000000 : ℝ)^83 ≤ (256877610373/6250000000000 : ℝ)^67 := by
    have hnat : (760425373 : ℕ)^83*6250000000000^67 ≤ 256877610373^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760425373 10000000000 256877610373 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097188317/10000000000 : ℝ)^83 ≤ (43394980533161/100000000000000 : ℝ)^67 := by
    have hnat : (5097188317 : ℕ)^83*100000000000000^67 ≤ 43394980533161^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097188317 10000000000 43394980533161 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5943892677/10000000000 : ℝ)^83 ≤ (52494977682497/100000000000000 : ℝ)^67 := by
    have hnat : (5943892677 : ℕ)^83*100000000000000^67 ≤ 52494977682497^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5943892677 10000000000 52494977682497 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-760425373/10000000000 : ℝ), (5097188317/10000000000 : ℝ), (5943892677/10000000000 : ℝ)] ![(256877610373/6250000000000 : ℝ), (43394980533161/100000000000000 : ℝ), (52494977682497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-760425373/10000000000 : ℝ)|^83 ≤ (256877610373/6250000000000 : ℝ)^67
        have hw : |(-760425373/10000000000 : ℝ)|=(760425373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5097188317/10000000000 : ℝ)|^83 ≤ (43394980533161/100000000000000 : ℝ)^67
        have hw : |(5097188317/10000000000 : ℝ)|=(5097188317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5943892677/10000000000 : ℝ)|^83 ≤ (52494977682497/100000000000000 : ℝ)^67
        have hw : |(5943892677/10000000000 : ℝ)|=(5943892677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4754533087/10000000000 : ℝ)*x 0 + (-253188063/2000000000 : ℝ)*x 1 + (1485205847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4754533087/10000000000 : ℝ)^83 ≤ (39810653494971/100000000000000 : ℝ)^67 := by
    have hnat : (4754533087 : ℕ)^83*100000000000000^67 ≤ 39810653494971^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754533087 10000000000 39810653494971 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253188063/2000000000 : ℝ)^83 ≤ (3863973645809/50000000000000 : ℝ)^67 := by
    have hnat : (253188063 : ℕ)^83*50000000000000^67 ≤ 3863973645809^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253188063 2000000000 3863973645809 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1485205847/2500000000 : ℝ)^83 ≤ (10492279839661/20000000000000 : ℝ)^67 := by
    have hnat : (1485205847 : ℕ)^83*20000000000000^67 ≤ 10492279839661^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485205847 2500000000 10492279839661 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4754533087/10000000000 : ℝ), (-253188063/2000000000 : ℝ), (1485205847/2500000000 : ℝ)] ![(39810653494971/100000000000000 : ℝ), (3863973645809/50000000000000 : ℝ), (10492279839661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4754533087/10000000000 : ℝ)|^83 ≤ (39810653494971/100000000000000 : ℝ)^67
        have hw : |(4754533087/10000000000 : ℝ)|=(4754533087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253188063/2000000000 : ℝ)|^83 ≤ (3863973645809/50000000000000 : ℝ)^67
        have hw : |(-253188063/2000000000 : ℝ)|=(253188063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1485205847/2500000000 : ℝ)|^83 ≤ (10492279839661/20000000000000 : ℝ)^67
        have hw : |(1485205847/2500000000 : ℝ)|=(1485205847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2970962377/5000000000 : ℝ)*x 0 + (637986499/1250000000 : ℝ)*x 1 + (-753071473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2970962377/5000000000 : ℝ)^83 ≤ (3279590489491/6250000000000 : ℝ)^67 := by
    have hnat : (2970962377 : ℕ)^83*6250000000000^67 ≤ 3279590489491^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970962377 5000000000 3279590489491 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (637986499/1250000000 : ℝ)^83 ≤ (43465692551121/100000000000000 : ℝ)^67 := by
    have hnat : (637986499 : ℕ)^83*100000000000000^67 ≤ 43465692551121^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637986499 1250000000 43465692551121 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753071473/10000000000 : ℝ)^83 ≤ (812171920471/20000000000000 : ℝ)^67 := by
    have hnat : (753071473 : ℕ)^83*20000000000000^67 ≤ 812171920471^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753071473 10000000000 812171920471 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2970962377/5000000000 : ℝ), (637986499/1250000000 : ℝ), (-753071473/10000000000 : ℝ)] ![(3279590489491/6250000000000 : ℝ), (43465692551121/100000000000000 : ℝ), (812171920471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2970962377/5000000000 : ℝ)|^83 ≤ (3279590489491/6250000000000 : ℝ)^67
        have hw : |(2970962377/5000000000 : ℝ)|=(2970962377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(637986499/1250000000 : ℝ)|^83 ≤ (43465692551121/100000000000000 : ℝ)^67
        have hw : |(637986499/1250000000 : ℝ)|=(637986499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-753071473/10000000000 : ℝ)|^83 ≤ (812171920471/20000000000000 : ℝ)^67
        have hw : |(-753071473/10000000000 : ℝ)|=(753071473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5833598163/10000000000 : ℝ)*x 0 + (30464813/78125000 : ℝ)*x 1 + (1228230741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5833598163/10000000000 : ℝ)^83 ≤ (256454754967/500000000000 : ℝ)^67 := by
    have hnat : (5833598163 : ℕ)^83*500000000000^67 ≤ 256454754967^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5833598163 10000000000 256454754967 500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30464813/78125000 : ℝ)^83 ≤ (15570726466439/50000000000000 : ℝ)^67 := by
    have hnat : (30464813 : ℕ)^83*50000000000000^67 ≤ 15570726466439^67*78125000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30464813 78125000 15570726466439 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228230741/5000000000 : ℝ)^83 ≤ (17567596056247/100000000000000 : ℝ)^67 := by
    have hnat : (1228230741 : ℕ)^83*100000000000000^67 ≤ 17567596056247^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228230741 5000000000 17567596056247 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5833598163/10000000000 : ℝ), (30464813/78125000 : ℝ), (1228230741/5000000000 : ℝ)] ![(256454754967/500000000000 : ℝ), (15570726466439/50000000000000 : ℝ), (17567596056247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5833598163/10000000000 : ℝ)|^83 ≤ (256454754967/500000000000 : ℝ)^67
        have hw : |(5833598163/10000000000 : ℝ)|=(5833598163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30464813/78125000 : ℝ)|^83 ≤ (15570726466439/50000000000000 : ℝ)^67
        have hw : |(30464813/78125000 : ℝ)|=(30464813/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1228230741/5000000000 : ℝ)|^83 ≤ (17567596056247/100000000000000 : ℝ)^67
        have hw : |(1228230741/5000000000 : ℝ)|=(1228230741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-355454497/5000000000 : ℝ)*x 0 + (1421996731/2500000000 : ℝ)*x 1 + (2695240607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355454497/5000000000 : ℝ)^83 ≤ (1890559471141/50000000000000 : ℝ)^67 := by
    have hnat : (355454497 : ℕ)^83*50000000000000^67 ≤ 1890559471141^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355454497 5000000000 1890559471141 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421996731/2500000000 : ℝ)^83 ≤ (497097109159/1000000000000 : ℝ)^67 := by
    have hnat : (1421996731 : ℕ)^83*1000000000000^67 ≤ 497097109159^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421996731 2500000000 497097109159 1000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695240607/5000000000 : ℝ)^83 ≤ (46509170132583/100000000000000 : ℝ)^67 := by
    have hnat : (2695240607 : ℕ)^83*100000000000000^67 ≤ 46509170132583^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695240607 5000000000 46509170132583 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355454497/5000000000 : ℝ), (1421996731/2500000000 : ℝ), (2695240607/5000000000 : ℝ)] ![(1890559471141/50000000000000 : ℝ), (497097109159/1000000000000 : ℝ), (46509170132583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355454497/5000000000 : ℝ)|^83 ≤ (1890559471141/50000000000000 : ℝ)^67
        have hw : |(-355454497/5000000000 : ℝ)|=(355454497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421996731/2500000000 : ℝ)|^83 ≤ (497097109159/1000000000000 : ℝ)^67
        have hw : |(1421996731/2500000000 : ℝ)|=(1421996731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695240607/5000000000 : ℝ)|^83 ≤ (46509170132583/100000000000000 : ℝ)^67
        have hw : |(2695240607/5000000000 : ℝ)|=(2695240607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5982131909/10000000000 : ℝ)*x 0 + (-710037073/10000000000 : ℝ)*x 1 + (254461001/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5982131909/10000000000 : ℝ)^83 ≤ (26456833647057/50000000000000 : ℝ)^67 := by
    have hnat : (5982131909 : ℕ)^83*50000000000000^67 ≤ 26456833647057^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5982131909 10000000000 26456833647057 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710037073/10000000000 : ℝ)^83 ≤ (3775374827197/100000000000000 : ℝ)^67 := by
    have hnat : (710037073 : ℕ)^83*100000000000000^67 ≤ 3775374827197^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710037073 10000000000 3775374827197 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254461001/500000000 : ℝ)^83 ≤ (43310957855691/100000000000000 : ℝ)^67 := by
    have hnat : (254461001 : ℕ)^83*100000000000000^67 ≤ 43310957855691^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254461001 500000000 43310957855691 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5982131909/10000000000 : ℝ), (-710037073/10000000000 : ℝ), (254461001/500000000 : ℝ)] ![(26456833647057/50000000000000 : ℝ), (3775374827197/100000000000000 : ℝ), (43310957855691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5982131909/10000000000 : ℝ)|^83 ≤ (26456833647057/50000000000000 : ℝ)^67
        have hw : |(5982131909/10000000000 : ℝ)|=(5982131909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-710037073/10000000000 : ℝ)|^83 ≤ (3775374827197/100000000000000 : ℝ)^67
        have hw : |(-710037073/10000000000 : ℝ)|=(710037073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254461001/500000000 : ℝ)|^83 ≤ (43310957855691/100000000000000 : ℝ)^67
        have hw : |(254461001/500000000 : ℝ)|=(254461001/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4706651209/10000000000 : ℝ)*x 0 + (1198576073/2000000000 : ℝ)*x 1 + (-628072827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4706651209/10000000000 : ℝ)^83 ≤ (2457161536479/6250000000000 : ℝ)^67 := by
    have hnat : (4706651209 : ℕ)^83*6250000000000^67 ≤ 2457161536479^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706651209 10000000000 2457161536479 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198576073/2000000000 : ℝ)^83 ≤ (10606293951393/20000000000000 : ℝ)^67 := by
    have hnat : (1198576073 : ℕ)^83*20000000000000^67 ≤ 10606293951393^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198576073 2000000000 10606293951393 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628072827/5000000000 : ℝ)^83 ≤ (1530789127423/20000000000000 : ℝ)^67 := by
    have hnat : (628072827 : ℕ)^83*20000000000000^67 ≤ 1530789127423^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628072827 5000000000 1530789127423 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4706651209/10000000000 : ℝ), (1198576073/2000000000 : ℝ), (-628072827/5000000000 : ℝ)] ![(2457161536479/6250000000000 : ℝ), (10606293951393/20000000000000 : ℝ), (1530789127423/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4706651209/10000000000 : ℝ)|^83 ≤ (2457161536479/6250000000000 : ℝ)^67
        have hw : |(4706651209/10000000000 : ℝ)|=(4706651209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198576073/2000000000 : ℝ)|^83 ≤ (10606293951393/20000000000000 : ℝ)^67
        have hw : |(1198576073/2000000000 : ℝ)|=(1198576073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-628072827/5000000000 : ℝ)|^83 ≤ (1530789127423/20000000000000 : ℝ)^67
        have hw : |(-628072827/5000000000 : ℝ)|=(628072827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322063_s2_s2_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2998580399/5000000000 : ℝ)*x 0 + (3162490913/10000000000 : ℝ)*x 1 + (23768633/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2998580399/5000000000 : ℝ)^83 ≤ (53078397112237/100000000000000 : ℝ)^67 := by
    have hnat : (2998580399 : ℕ)^83*100000000000000^67 ≤ 53078397112237^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998580399 5000000000 53078397112237 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3162490913/10000000000 : ℝ)^83 ≤ (12011667430749/50000000000000 : ℝ)^67 := by
    have hnat : (3162490913 : ℕ)^83*50000000000000^67 ≤ 12011667430749^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162490913 10000000000 12011667430749 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23768633/78125000 : ℝ)^83 ≤ (22898268010653/100000000000000 : ℝ)^67 := by
    have hnat : (23768633 : ℕ)^83*100000000000000^67 ≤ 22898268010653^67*78125000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23768633 78125000 22898268010653 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2998580399/5000000000 : ℝ), (3162490913/10000000000 : ℝ), (23768633/78125000 : ℝ)] ![(53078397112237/100000000000000 : ℝ), (12011667430749/50000000000000 : ℝ), (22898268010653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2998580399/5000000000 : ℝ)|^83 ≤ (53078397112237/100000000000000 : ℝ)^67
        have hw : |(2998580399/5000000000 : ℝ)|=(2998580399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3162490913/10000000000 : ℝ)|^83 ≤ (12011667430749/50000000000000 : ℝ)^67
        have hw : |(3162490913/10000000000 : ℝ)|=(3162490913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23768633/78125000 : ℝ)|^83 ≤ (22898268010653/100000000000000 : ℝ)^67
        have hw : |(23768633/78125000 : ℝ)|=(23768633/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322063_s2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((22899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9293/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9293/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((697/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(697/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14137/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14137/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3391/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (22899/50000 : ℝ) ^ (41/8 : ℝ) ≤ (913710008902087677/50000000000000000000 : ℝ) := by
    have hpowers : (22899/50000 : ℝ)^41 ≤ (913710008902087677/50000000000000000000 : ℝ)^8 := by
      have hnat : (22899 : ℕ)^41*50000000000000000000^8 ≤ 913710008902087677^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22899 50000 913710008902087677 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22899/50000 : ℝ)) (X := (913710008902087677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (50913710008902087677/50000000000000000000 : ℝ) ≤ (78401543688909/78125000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50913710008902087677/50000000000000000000 : ℝ)^8 ≤ (78401543688909/78125000000000 : ℝ)^41 := by
      have hnat : (50913710008902087677 : ℕ)^8*78125000000000^41 ≤ 78401543688909^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50913710008902087677 50000000000000000000 78401543688909 78125000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78401543688909/78125000000000 : ℝ)) (X := (50913710008902087677/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (25913710008902087677/25000000000000000000 : ℝ) ≤ (2014057503903673/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25913710008902087677/25000000000000000000 : ℝ)^8 ≤ (2014057503903673/2000000000000000 : ℝ)^41 := by
      have hnat : (25913710008902087677 : ℕ)^8*2000000000000000^41 ≤ 2014057503903673^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25913710008902087677 25000000000000000000 2014057503903673 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2014057503903673/2000000000000000 : ℝ)) (X := (25913710008902087677/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(276543688909/35779687500000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(34889927338013/4579800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (22899/50000 : ℝ)) (alpha := (276543688909/35779687500000 : ℝ)) (beta := (34889927338013/4579800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22899/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(276543688909/35779687500000 : ℝ)*((1 : ℝ)*pair X 0 1)+(34889927338013/4579800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (9293/20000 : ℝ) ^ (41/8 : ℝ) ≤ (983989477988526511/50000000000000000000 : ℝ) := by
    have hpowers : (9293/20000 : ℝ)^41 ≤ (983989477988526511/50000000000000000000 : ℝ)^8 := by
      have hnat : (9293 : ℕ)^41*50000000000000000000^8 ≤ 983989477988526511^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9293 20000 983989477988526511 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9293/20000 : ℝ)) (X := (983989477988526511/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (50983989477988526511/50000000000000000000 : ℝ) ≤ (10038099019691687/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50983989477988526511/50000000000000000000 : ℝ)^8 ≤ (10038099019691687/10000000000000000 : ℝ)^41 := by
      have hnat : (50983989477988526511 : ℕ)^8*10000000000000000^41 ≤ 10038099019691687^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50983989477988526511 50000000000000000000 10038099019691687 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038099019691687/10000000000000000 : ℝ)) (X := (50983989477988526511/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (25983989477988526511/25000000000000000000 : ℝ) ≤ (251890268172823/250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25983989477988526511/25000000000000000000 : ℝ)^8 ≤ (251890268172823/250000000000000 : ℝ)^41 := by
      have hnat : (25983989477988526511 : ℕ)^8*250000000000000^41 ≤ 251890268172823^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25983989477988526511 25000000000000000000 251890268172823 250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251890268172823/250000000000000 : ℝ)) (X := (25983989477988526511/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(38099019691687/4646500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(37511707221233/4646500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (9293/20000 : ℝ)) (alpha := (38099019691687/4646500000000000 : ℝ)) (beta := (37511707221233/4646500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9293/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(38099019691687/4646500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(37511707221233/4646500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (22209/50000 : ℝ) ^ (41/8 : ℝ) ≤ (1562211655830566553/100000000000000000000 : ℝ) := by
    have hpowers : (22209/50000 : ℝ)^41 ≤ (1562211655830566553/100000000000000000000 : ℝ)^8 := by
      have hnat : (22209 : ℕ)^41*100000000000000000000^8 ≤ 1562211655830566553^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22209 50000 1562211655830566553 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22209/50000 : ℝ)) (X := (1562211655830566553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (101562211655830566553/100000000000000000000 : ℝ) ≤ (1253786540049829/1250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (101562211655830566553/100000000000000000000 : ℝ)^8 ≤ (1253786540049829/1250000000000000 : ℝ)^41 := by
      have hnat : (101562211655830566553 : ℕ)^8*1250000000000000^41 ≤ 1253786540049829^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101562211655830566553 100000000000000000000 1253786540049829 1250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253786540049829/1250000000000000 : ℝ)) (X := (101562211655830566553/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (51562211655830566553/50000000000000000000 : ℝ) ≤ (10060211898562139/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (51562211655830566553/50000000000000000000 : ℝ)^8 ≤ (10060211898562139/10000000000000000 : ℝ)^41 := by
      have hnat : (51562211655830566553 : ℕ)^8*10000000000000000^41 ≤ 10060211898562139^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51562211655830566553 50000000000000000000 10060211898562139 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060211898562139/10000000000000000 : ℝ)) (X := (51562211655830566553/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3786540049829/555225000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9973192721169/1480600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (22209/50000 : ℝ)) (alpha := (3786540049829/555225000000000 : ℝ)) (beta := (9973192721169/1480600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22209/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3786540049829/555225000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9973192721169/1480600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-666668913/5000000000 : ℝ)*X 0 0+(1331454767/2500000000 : ℝ)*X 0 1+(5337181099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5326276449/10000000000 : ℝ)*X 1 0+(-267390689/2000000000 : ℝ)*X 1 1+(533412673/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5335318933/10000000000 : ℝ)*X 2 0+(106654163/200000000 : ℝ)*X 2 1+(-66316793/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1030677851/2500000000 : ℝ)*X 0 0+(515142043/1250000000 : ℝ)*X 0 1+(4114919321/10000000000 : ℝ)*X 0 2+(1030677851/2500000000 : ℝ)*X 1 0+(515142043/1250000000 : ℝ)*X 1 1+(4114919321/10000000000 : ℝ)*X 1 2+(1030677851/2500000000 : ℝ)*X 2 0+(515142043/1250000000 : ℝ)*X 2 1+(4114919321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-634209869/5000000000 : ℝ)*X 0 0+(2369179071/5000000000 : ℝ)*X 0 1+(297721803/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1018074817/2000000000 : ℝ)*X 1 0+(-758941281/10000000000 : ℝ)*X 1 1+(2975683617/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2454232609/5000000000 : ℝ)*X 2 0+(3067598107/5000000000 : ℝ)*X 2 1+(-742528093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((139504439/312500000 : ℝ)*X 0 0+(5331385789/10000000000 : ℝ)*X 0 1+(2426305897/10000000000 : ℝ)*X 0 2+(139504439/312500000 : ℝ)*X 1 0+(5331385789/10000000000 : ℝ)*X 1 1+(2426305897/10000000000 : ℝ)*X 1 2+(139504439/312500000 : ℝ)*X 2 0+(5331385789/10000000000 : ℝ)*X 2 1+(2426305897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-760425373/10000000000 : ℝ)*X 0 0+(5097188317/10000000000 : ℝ)*X 0 1+(5943892677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4754533087/10000000000 : ℝ)*X 1 0+(-253188063/2000000000 : ℝ)*X 1 1+(1485205847/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2970962377/5000000000 : ℝ)*X 2 0+(637986499/1250000000 : ℝ)*X 2 1+(-753071473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5833598163/10000000000 : ℝ)*X 0 0+(30464813/78125000 : ℝ)*X 0 1+(1228230741/5000000000 : ℝ)*X 0 2+(5833598163/10000000000 : ℝ)*X 1 0+(30464813/78125000 : ℝ)*X 1 1+(1228230741/5000000000 : ℝ)*X 1 2+(5833598163/10000000000 : ℝ)*X 2 0+(30464813/78125000 : ℝ)*X 2 1+(1228230741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-355454497/5000000000 : ℝ)*X 0 0+(1421996731/2500000000 : ℝ)*X 0 1+(2695240607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5982131909/10000000000 : ℝ)*X 1 0+(-710037073/10000000000 : ℝ)*X 1 1+(254461001/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4706651209/10000000000 : ℝ)*X 2 0+(1198576073/2000000000 : ℝ)*X 2 1+(-628072827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2998580399/5000000000 : ℝ)*X 0 0+(3162490913/10000000000 : ℝ)*X 0 1+(23768633/78125000 : ℝ)*X 0 2+(2998580399/5000000000 : ℝ)*X 1 0+(3162490913/10000000000 : ℝ)*X 1 1+(23768633/78125000 : ℝ)*X 1 2+(2998580399/5000000000 : ℝ)*X 2 0+(3162490913/10000000000 : ℝ)*X 2 1+(23768633/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((697/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(697/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (257020128264226236233097589367/15444719735500000000000000000000000 : ℝ) := by norm_num
    linear_combination (433977/125000000000 : ℝ)*(base50) + (79748163107/500000000000 : ℝ)*(base60) + (5628775197307/1000000000000 : ℝ)*(major_s2_0) + (5628775197307/1000000000000 : ℝ)*(major_s2_1) + (5628775197307/1000000000000 : ℝ)*(major_s2_2) + (22378857/500000000000 : ℝ)*(sp_s2_0) + (534871/31250000000 : ℝ)*(sp_s2_6) + (8340829567669/1000000000000 : ℝ)*(sp_s2_7) + (8340802283421/1000000000000 : ℝ)*(sp_s2_8) + (8340814714541/1000000000000 : ℝ)*(sp_s2_9) + (4666556539/1600000000 : ℝ)*(sp_s2_13) + (1736543/31250000000 : ℝ)*(sp_s2_14) + (127611339/1000000000000 : ℝ)*(sp_s2_15) + (57590109/500000000000 : ℝ)*(sp_s2_23) + (2916614952747/1000000000000 : ℝ)*(f.failure) + (208523247369/25000000000 : ℝ)*(f.sum) + (20808605664091384661/103194118500000000000000000000000 : ℝ)*base63 + (1164603481926783/1480600000000000000000000000 : ℝ)*base65 + (2239317596252281/4646500000000000000000000000 : ℝ)*base67 + (15312095279971/69403125000000000000000000 : ℝ)*base69 + (257678952029564237/1994368200000000000000000000000 : ℝ)*base71 + (44026893740803/269400000000000000000000000 : ℝ)*base73 + (4478630986242709/4646500000000000000000000000 : ℝ)*base75 + (53492568144703/67350000000000000000000000 : ℝ)*base77 + (3716265296283001991/12517671000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (5647/10000000000000000 : ℝ)*base86 + (5647/10000000000000000 : ℝ)*base88 + (5647/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14137/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14137/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33076870352017411622207019/5650709900000000000000000000000 : ℝ) := by norm_num
    linear_combination (566429/250000000000 : ℝ)*(base60) + (5728304522891/1000000000000 : ℝ)*(major_s2_0) + (5728304522891/1000000000000 : ℝ)*(major_s2_1) + (5728304522891/1000000000000 : ℝ)*(major_s2_2) + (2578591/62500000000 : ℝ)*(sp_s2_0) + (2401931/50000000000 : ℝ)*(sp_s2_1) + (27569067/500000000000 : ℝ)*(sp_s2_2) + (19208667/1000000000000 : ℝ)*(sp_s2_7) + (5079939/200000000000 : ℝ)*(sp_s2_8) + (8488359404827/1000000000000 : ℝ)*(sp_s2_14) + (2122086608159/250000000000 : ℝ)*(sp_s2_15) + (8488364732817/1000000000000 : ℝ)*(sp_s2_16) + (2968139254299/1000000000000 : ℝ)*(sp_s2_20) + (9593867/200000000000 : ℝ)*(sp_s2_27) + (1484093611817/500000000000 : ℝ)*(f.failure) + (8488419870951/1000000000000 : ℝ)*(f.sum) + (59275854526534897907/103194118500000000000000000000000 : ℝ)*base62 + (1396076596171259/1480600000000000000000000000 : ℝ)*base65 + (3135747151649953/4646500000000000000000000000 : ℝ)*base67 + (41536532793269/138806250000000000000000000 : ℝ)*base68 + (9221888003168500577/33904259400000000000000000000000 : ℝ)*base71 + (540522012450703/4579800000000000000000000000 : ℝ)*base73 + (162955942939567/4646500000000000000000000000 : ℝ)*base75 + (141854366189683/1144950000000000000000000000 : ℝ)*base77 + (17808790359029421611/212800407000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1283/5000000000000000 : ℝ)*base87 + (1283/5000000000000000 : ℝ)*base89 + (1283/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3391/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48225935798264357346412560369/4102503679742187500000000000000000 : ℝ) := by norm_num
    linear_combination (1305079/200000000000 : ℝ)*(base15) + (232095628241/1000000000000 : ℝ)*(base40) + (164141761911/31250000000 : ℝ)*(major_s2_0) + (164141761911/31250000000 : ℝ)*(major_s2_1) + (164141761911/31250000000 : ℝ)*(major_s2_2) + (2978189/40000000000 : ℝ)*(sp_s2_0) + (73566241/1000000000000 : ℝ)*(sp_s2_1) + (32640531/1000000000000 : ℝ)*(sp_s2_2) + (12675591/250000000000 : ℝ)*(sp_s2_9) + (34274493/500000000000 : ℝ)*(sp_s2_20) + (3891665964683/500000000000 : ℝ)*(sp_s2_21) + (1556665258491/200000000000 : ℝ)*(sp_s2_22) + (7783323041197/1000000000000 : ℝ)*(sp_s2_23) + (1360796955403/500000000000 : ℝ)*(sp_s2_27) + (170103903737/62500000000 : ℝ)*(f.failure) + (1945851596023/250000000000 : ℝ)*(f.sum) + (1159627528470877321/4299754937500000000000000000000 : ℝ)*base62 + (58314168728841/185075000000000000000000000 : ℝ)*base65 + (797470946059333/2323250000000000000000000000 : ℝ)*base67 + (77980006584011/185075000000000000000000000 : ℝ)*base69 + (215169683815368081/1412677475000000000000000000000 : ℝ)*base71 + (41458958601021/190825000000000000000000000 : ℝ)*base72 + (349212535894419/1161625000000000000000000000 : ℝ)*base74 + (23028058053347/381650000000000000000000000 : ℝ)*base77 + (3059110860084519183/8866683625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (363/625000000000000 : ℝ)*base87 + (363/625000000000000 : ℝ)*base89 + (363/625000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((22899/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22899/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9293/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9293/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((697/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(697/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14137/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14137/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3391/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3391/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322063_s2 p hpa hpb X hX hprev1

#print axioms solution
