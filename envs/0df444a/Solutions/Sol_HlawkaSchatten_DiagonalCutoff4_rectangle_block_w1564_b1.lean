-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:18.95082+00:00
-- url     : https://prove2.me/submissions/246560db-4cc9-4615-ab82-34d66fa9d97b

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
theorem support_rectangle_w1564_s3_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179357633/1000000000 : ℝ)*x 0 + (2714173419/5000000000 : ℝ)*x 1 + (652279627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179357633/1000000000 : ℝ)^4625 ≤ (11002809002277/100000000000000 : ℝ)^3601 := by
    have hnat : (179357633 : ℕ)^4625*100000000000000^3601 ≤ 11002809002277^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179357633 1000000000 11002809002277 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714173419/5000000000 : ℝ)^4625 ≤ (22813200705619/50000000000000 : ℝ)^3601 := by
    have hnat : (2714173419 : ℕ)^4625*50000000000000^3601 ≤ 22813200705619^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714173419 5000000000 22813200705619 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652279627/1250000000 : ℝ)^4625 ≤ (21685394786939/50000000000000 : ℝ)^3601 := by
    have hnat : (652279627 : ℕ)^4625*50000000000000^3601 ≤ 21685394786939^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652279627 1250000000 21685394786939 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179357633/1000000000 : ℝ), (2714173419/5000000000 : ℝ), (652279627/1250000000 : ℝ)] ![(11002809002277/100000000000000 : ℝ), (22813200705619/50000000000000 : ℝ), (21685394786939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179357633/1000000000 : ℝ)|^4625 ≤ (11002809002277/100000000000000 : ℝ)^3601
        have hw : |(-179357633/1000000000 : ℝ)|=(179357633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714173419/5000000000 : ℝ)|^4625 ≤ (22813200705619/50000000000000 : ℝ)^3601
        have hw : |(2714173419/5000000000 : ℝ)|=(2714173419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652279627/1250000000 : ℝ)|^4625 ≤ (21685394786939/50000000000000 : ℝ)^3601
        have hw : |(652279627/1250000000 : ℝ)|=(652279627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674516321/5000000000 : ℝ)*x 0 + (-950558689/5000000000 : ℝ)*x 1 + (1304559241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674516321/5000000000 : ℝ)^4625 ≤ (44771960889603/100000000000000 : ℝ)^3601 := by
    have hnat : (2674516321 : ℕ)^4625*100000000000000^3601 ≤ 44771960889603^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674516321 5000000000 44771960889603 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950558689/5000000000 : ℝ)^4625 ≤ (11857250069383/100000000000000 : ℝ)^3601 := by
    have hnat : (950558689 : ℕ)^4625*100000000000000^3601 ≤ 11857250069383^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950558689 5000000000 11857250069383 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304559241/2500000000 : ℝ)^4625 ≤ (21685394509393/50000000000000 : ℝ)^3601 := by
    have hnat : (1304559241 : ℕ)^4625*50000000000000^3601 ≤ 21685394509393^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304559241 2500000000 21685394509393 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674516321/5000000000 : ℝ), (-950558689/5000000000 : ℝ), (1304559241/2500000000 : ℝ)] ![(44771960889603/100000000000000 : ℝ), (11857250069383/100000000000000 : ℝ), (21685394509393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674516321/5000000000 : ℝ)|^4625 ≤ (44771960889603/100000000000000 : ℝ)^3601
        have hw : |(2674516321/5000000000 : ℝ)|=(2674516321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950558689/5000000000 : ℝ)|^4625 ≤ (11857250069383/100000000000000 : ℝ)^3601
        have hw : |(-950558689/5000000000 : ℝ)|=(950558689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304559241/2500000000 : ℝ)|^4625 ≤ (21685394509393/50000000000000 : ℝ)^3601
        have hw : |(1304559241/2500000000 : ℝ)|=(1304559241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668629057/1250000000 : ℝ)*x 0 + (2609118547/5000000000 : ℝ)*x 1 + (-380223491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668629057/1250000000 : ℝ)^4625 ≤ (11192989722513/25000000000000 : ℝ)^3601 := by
    have hnat : (668629057 : ℕ)^4625*25000000000000^3601 ≤ 11192989722513^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668629057 1250000000 11192989722513 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609118547/5000000000 : ℝ)^4625 ≤ (43370790406517/100000000000000 : ℝ)^3601 := by
    have hnat : (2609118547 : ℕ)^4625*100000000000000^3601 ≤ 43370790406517^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609118547 5000000000 43370790406517 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380223491/2000000000 : ℝ)^4625 ≤ (11857250686197/100000000000000 : ℝ)^3601 := by
    have hnat : (380223491 : ℕ)^4625*100000000000000^3601 ≤ 11857250686197^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380223491 2000000000 11857250686197 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668629057/1250000000 : ℝ), (2609118547/5000000000 : ℝ), (-380223491/2000000000 : ℝ)] ![(11192989722513/25000000000000 : ℝ), (43370790406517/100000000000000 : ℝ), (11857250686197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668629057/1250000000 : ℝ)|^4625 ≤ (11192989722513/25000000000000 : ℝ)^3601
        have hw : |(668629057/1250000000 : ℝ)|=(668629057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609118547/5000000000 : ℝ)|^4625 ≤ (43370790406517/100000000000000 : ℝ)^3601
        have hw : |(2609118547/5000000000 : ℝ)|=(2609118547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380223491/2000000000 : ℝ)|^4625 ≤ (11857250686197/100000000000000 : ℝ)^3601
        have hw : |(-380223491/2000000000 : ℝ)|=(380223491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061496551/2500000000 : ℝ)*x 0 + (2002427811/5000000000 : ℝ)*x 1 + (2249403163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061496551/2500000000 : ℝ)^4625 ≤ (33280400067669/100000000000000 : ℝ)^3601 := by
    have hnat : (1061496551 : ℕ)^4625*100000000000000^3601 ≤ 33280400067669^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061496551 2500000000 33280400067669 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002427811/5000000000 : ℝ)^4625 ≤ (3859102467963/12500000000000 : ℝ)^3601 := by
    have hnat : (2002427811 : ℕ)^4625*12500000000000^3601 ≤ 3859102467963^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002427811 5000000000 3859102467963 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249403163/5000000000 : ℝ)^4625 ≤ (17923390084987/50000000000000 : ℝ)^3601 := by
    have hnat : (2249403163 : ℕ)^4625*50000000000000^3601 ≤ 17923390084987^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249403163 5000000000 17923390084987 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061496551/2500000000 : ℝ), (2002427811/5000000000 : ℝ), (2249403163/5000000000 : ℝ)] ![(33280400067669/100000000000000 : ℝ), (3859102467963/12500000000000 : ℝ), (17923390084987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061496551/2500000000 : ℝ)|^4625 ≤ (33280400067669/100000000000000 : ℝ)^3601
        have hw : |(1061496551/2500000000 : ℝ)|=(1061496551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002427811/5000000000 : ℝ)|^4625 ≤ (3859102467963/12500000000000 : ℝ)^3601
        have hw : |(2002427811/5000000000 : ℝ)|=(2002427811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249403163/5000000000 : ℝ)|^4625 ≤ (17923390084987/50000000000000 : ℝ)^3601
        have hw : |(2249403163/5000000000 : ℝ)|=(2249403163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1793604607/10000000000 : ℝ)*x 0 + (2609674053/5000000000 : ℝ)*x 1 + (2713613723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793604607/10000000000 : ℝ)^4625 ≤ (85961185921/781250000000 : ℝ)^3601 := by
    have hnat : (1793604607 : ℕ)^4625*781250000000^3601 ≤ 85961185921^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793604607 10000000000 85961185921 781250000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609674053/5000000000 : ℝ)^4625 ≤ (43382650661907/100000000000000 : ℝ)^3601 := by
    have hnat : (2609674053 : ℕ)^4625*100000000000000^3601 ≤ 43382650661907^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609674053 5000000000 43382650661907 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713613723/5000000000 : ℝ)^4625 ≤ (22807158761379/50000000000000 : ℝ)^3601 := by
    have hnat : (2713613723 : ℕ)^4625*50000000000000^3601 ≤ 22807158761379^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713613723 5000000000 22807158761379 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1793604607/10000000000 : ℝ), (2609674053/5000000000 : ℝ), (2713613723/5000000000 : ℝ)] ![(85961185921/781250000000 : ℝ), (43382650661907/100000000000000 : ℝ), (22807158761379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1793604607/10000000000 : ℝ)|^4625 ≤ (85961185921/781250000000 : ℝ)^3601
        have hw : |(-1793604607/10000000000 : ℝ)|=(1793604607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609674053/5000000000 : ℝ)|^4625 ≤ (43382650661907/100000000000000 : ℝ)^3601
        have hw : |(2609674053/5000000000 : ℝ)|=(2609674053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713613723/5000000000 : ℝ)|^4625 ≤ (22807158761379/50000000000000 : ℝ)^3601
        have hw : |(2713613723/5000000000 : ℝ)|=(2713613723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323370881/2500000000 : ℝ)*x 0 + (-338425367/2000000000 : ℝ)*x 1 + (2713613833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323370881/2500000000 : ℝ)^4625 ≤ (44175676663801/100000000000000 : ℝ)^3601 := by
    have hnat : (1323370881 : ℕ)^4625*100000000000000^3601 ≤ 44175676663801^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323370881 2500000000 44175676663801 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338425367/2000000000 : ℝ)^4625 ≤ (10210003426449/100000000000000 : ℝ)^3601 := by
    have hnat : (338425367 : ℕ)^4625*100000000000000^3601 ≤ 10210003426449^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338425367 2000000000 10210003426449 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713613833/5000000000 : ℝ)^4625 ≤ (22807159948799/50000000000000 : ℝ)^3601 := by
    have hnat : (2713613833 : ℕ)^4625*50000000000000^3601 ≤ 22807159948799^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713613833 5000000000 22807159948799 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323370881/2500000000 : ℝ), (-338425367/2000000000 : ℝ), (2713613833/5000000000 : ℝ)] ![(44175676663801/100000000000000 : ℝ), (10210003426449/100000000000000 : ℝ), (22807159948799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323370881/2500000000 : ℝ)|^4625 ≤ (44175676663801/100000000000000 : ℝ)^3601
        have hw : |(1323370881/2500000000 : ℝ)|=(1323370881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338425367/2000000000 : ℝ)|^4625 ≤ (10210003426449/100000000000000 : ℝ)^3601
        have hw : |(-338425367/2000000000 : ℝ)|=(338425367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713613833/5000000000 : ℝ)|^4625 ≤ (22807159948799/50000000000000 : ℝ)^3601
        have hw : |(2713613833/5000000000 : ℝ)|=(2713613833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293483659/10000000000 : ℝ)*x 0 + (5427227549/10000000000 : ℝ)*x 1 + (-1692126811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293483659/10000000000 : ℝ)^4625 ≤ (22087839055393/50000000000000 : ℝ)^3601 := by
    have hnat : (5293483659 : ℕ)^4625*50000000000000^3601 ≤ 22087839055393^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293483659 10000000000 22087839055393 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427227549/10000000000 : ℝ)^4625 ≤ (9122863726923/20000000000000 : ℝ)^3601 := by
    have hnat : (5427227549 : ℕ)^4625*20000000000000^3601 ≤ 9122863726923^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427227549 10000000000 9122863726923 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1692126811/10000000000 : ℝ)^4625 ≤ (5105001620229/50000000000000 : ℝ)^3601 := by
    have hnat : (1692126811 : ℕ)^4625*50000000000000^3601 ≤ 5105001620229^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692126811 10000000000 5105001620229 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293483659/10000000000 : ℝ), (5427227549/10000000000 : ℝ), (-1692126811/10000000000 : ℝ)] ![(22087839055393/50000000000000 : ℝ), (9122863726923/20000000000000 : ℝ), (5105001620229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293483659/10000000000 : ℝ)|^4625 ≤ (22087839055393/50000000000000 : ℝ)^3601
        have hw : |(5293483659/10000000000 : ℝ)|=(5293483659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427227549/10000000000 : ℝ)|^4625 ≤ (9122863726923/20000000000000 : ℝ)^3601
        have hw : |(5427227549/10000000000 : ℝ)|=(5427227549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1692126811/10000000000 : ℝ)|^4625 ≤ (5105001620229/50000000000000 : ℝ)^3601
        have hw : |(-1692126811/10000000000 : ℝ)|=(1692126811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s3_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123026421/5000000000 : ℝ)*x 0 + (899238881/2000000000 : ℝ)*x 1 + (1001871787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123026421/5000000000 : ℝ)^4625 ≤ (16640535455803/50000000000000 : ℝ)^3601 := by
    have hnat : (2123026421 : ℕ)^4625*50000000000000^3601 ≤ 16640535455803^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123026421 5000000000 16640535455803 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899238881/2000000000 : ℝ)^4625 ≤ (35820052219899/100000000000000 : ℝ)^3601 := by
    have hnat : (899238881 : ℕ)^4625*100000000000000^3601 ≤ 35820052219899^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899238881 2000000000 35820052219899 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001871787/2500000000 : ℝ)^4625 ≤ (1544943842787/5000000000000 : ℝ)^3601 := by
    have hnat : (1001871787 : ℕ)^4625*5000000000000^3601 ≤ 1544943842787^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001871787 2500000000 1544943842787 5000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123026421/5000000000 : ℝ), (899238881/2000000000 : ℝ), (1001871787/2500000000 : ℝ)] ![(16640535455803/50000000000000 : ℝ), (35820052219899/100000000000000 : ℝ), (1544943842787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123026421/5000000000 : ℝ)|^4625 ≤ (16640535455803/50000000000000 : ℝ)^3601
        have hw : |(2123026421/5000000000 : ℝ)|=(2123026421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899238881/2000000000 : ℝ)|^4625 ≤ (35820052219899/100000000000000 : ℝ)^3601
        have hw : |(899238881/2000000000 : ℝ)|=(899238881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001871787/2500000000 : ℝ)|^4625 ≤ (1544943842787/5000000000000 : ℝ)^3601
        have hw : |(1001871787/2500000000 : ℝ)|=(1001871787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11067/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7761/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3957/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3957/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3957/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3957/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3957/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3957/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2157/20000 : ℝ) ^ (4623/1024 : ℝ) ≤ (1075135018366369/25000000000000000000 : ℝ) := by
    have hpowers : (2157/20000 : ℝ)^4623 ≤ (1075135018366369/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2157 : ℕ)^4623*25000000000000000000^1024 ≤ 1075135018366369^1024*20000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2157 20000 1075135018366369 25000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2157/20000 : ℝ)) (X := (1075135018366369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3957/25000 : ℝ) ^ (4623/1024 : ℝ) ≤ (24304686835056191/100000000000000000000 : ℝ) := by
    have hpowers : (3957/25000 : ℝ)^4623 ≤ (24304686835056191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3957 : ℕ)^4623*100000000000000000000^1024 ≤ 24304686835056191^1024*25000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3957 25000 24304686835056191 100000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3957/25000 : ℝ)) (X := (24304686835056191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501075135018366369/12500000000000000000 : ℝ) ≤ (10000190508570479/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (12501075135018366369/12500000000000000000 : ℝ)^1024 ≤ (10000190508570479/10000000000000000 : ℝ)^4623 := by
      have hnat : (12501075135018366369 : ℕ)^1024*10000000000000000^4623 ≤ 10000190508570479^4623*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501075135018366369 12500000000000000000 10000190508570479 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000190508570479/10000000000000000 : ℝ)) (X := (12501075135018366369/12500000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028605226908521667/100000000000000000000 : ℝ) ≤ (5000316769320759/5000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (100028605226908521667/100000000000000000000 : ℝ)^1024 ≤ (5000316769320759/5000000000000000 : ℝ)^4623 := by
      have hnat : (100028605226908521667 : ℕ)^1024*5000000000000000^4623 ≤ 5000316769320759^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028605226908521667 100000000000000000000 5000316769320759 5000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000316769320759/5000000000000000 : ℝ)) (X := (100028605226908521667/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024304686835056191/50000000000000000000 : ℝ) ≤ (10001076568712557/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (50024304686835056191/50000000000000000000 : ℝ)^1024 ≤ (10001076568712557/10000000000000000 : ℝ)^4623 := by
      have hnat : (50024304686835056191 : ℕ)^1024*10000000000000000^4623 ≤ 10001076568712557^4623*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024304686835056191 50000000000000000000 10001076568712557 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001076568712557/10000000000000000 : ℝ)) (X := (50024304686835056191/50000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1075135018366369/25000000000000000000 : ℝ) ≤ ((16807134858696204789/16810000000000000000 : ℝ)+2*(443030071039/504300000000000 : ℝ)*(2157/20000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (16807134858696204789/16810000000000000000 : ℝ)+2*(443030071039/504300000000000 : ℝ)*(2157/20000 : ℝ)=(10000190508570479/10000000000000000 : ℝ) by norm_num, show 1+2*(1075135018366369/25000000000000000000 : ℝ)=(12501075135018366369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24304686835056191/100000000000000000000 : ℝ)+(1075135018366369/25000000000000000000 : ℝ) ≤ ((16807134858696204789/16810000000000000000 : ℝ)+(443030071039/504300000000000 : ℝ)*((3957/25000 : ℝ)+(2157/20000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (16807134858696204789/16810000000000000000 : ℝ)+(443030071039/504300000000000 : ℝ)*((3957/25000 : ℝ)+(2157/20000 : ℝ))=(5000316769320759/5000000000000000 : ℝ) by norm_num, show 1+(24304686835056191/100000000000000000000 : ℝ)+(1075135018366369/25000000000000000000 : ℝ)=(100028605226908521667/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24304686835056191/100000000000000000000 : ℝ) ≤ ((16807134858696204789/16810000000000000000 : ℝ)+2*(443030071039/504300000000000 : ℝ)*(3957/25000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (16807134858696204789/16810000000000000000 : ℝ)+2*(443030071039/504300000000000 : ℝ)*(3957/25000 : ℝ)=(10001076568712557/10000000000000000 : ℝ) by norm_num, show 1+2*(24304686835056191/100000000000000000000 : ℝ)=(50024304686835056191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16807134858696204789/16810000000000000000 : ℝ)*(X 1 0+X 2 0)+(443030071039/504300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (3957/25000 : ℝ)) (c := (16807134858696204789/16810000000000000000 : ℝ)) (alpha := (443030071039/504300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16807134858696204789/16810000000000000000 : ℝ)*(X 0 1+X 2 1)+(443030071039/504300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (3957/25000 : ℝ)) (c := (16807134858696204789/16810000000000000000 : ℝ)) (alpha := (443030071039/504300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16807134858696204789/16810000000000000000 : ℝ)*(X 0 2+X 1 2)+(443030071039/504300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (3957/25000 : ℝ)) (c := (16807134858696204789/16810000000000000000 : ℝ)) (alpha := (443030071039/504300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-179357633/1000000000 : ℝ)*X 0 0+(2714173419/5000000000 : ℝ)*X 0 1+(652279627/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674516321/5000000000 : ℝ)*X 1 0+(-950558689/5000000000 : ℝ)*X 1 1+(1304559241/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668629057/1250000000 : ℝ)*X 2 0+(2609118547/5000000000 : ℝ)*X 2 1+(-380223491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061496551/2500000000 : ℝ)*X 0 0+(2002427811/5000000000 : ℝ)*X 0 1+(2249403163/5000000000 : ℝ)*X 0 2+(1061496551/2500000000 : ℝ)*X 1 0+(2002427811/5000000000 : ℝ)*X 1 1+(2249403163/5000000000 : ℝ)*X 1 2+(1061496551/2500000000 : ℝ)*X 2 0+(2002427811/5000000000 : ℝ)*X 2 1+(2249403163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1793604607/10000000000 : ℝ)*X 0 0+(2609674053/5000000000 : ℝ)*X 0 1+(2713613723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323370881/2500000000 : ℝ)*X 1 0+(-338425367/2000000000 : ℝ)*X 1 1+(2713613833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293483659/10000000000 : ℝ)*X 2 0+(5427227549/10000000000 : ℝ)*X 2 1+(-1692126811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123026421/5000000000 : ℝ)*X 0 0+(899238881/2000000000 : ℝ)*X 0 1+(1001871787/2500000000 : ℝ)*X 0 2+(2123026421/5000000000 : ℝ)*X 1 0+(899238881/2000000000 : ℝ)*X 1 1+(1001871787/2500000000 : ℝ)*X 1 2+(2123026421/5000000000 : ℝ)*X 2 0+(899238881/2000000000 : ℝ)*X 2 1+(1001871787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8255269567094336519223/1050625000000000000000000000 : ℝ) := by norm_num
    linear_combination (720994183/50000000000000 : ℝ)*(base19) + (144658933/12500000000000 : ℝ)*(base23) + (63770061/100000000000000 : ℝ)*(lower2) + (127224547/50000000000000 : ℝ)*(upper3) + (66536053/100000000000000 : ℝ)*(upper5) + (3391986647685849/100000000000000 : ℝ)*(major0) + (3391986647685849/100000000000000 : ℝ)*(major1) + (67839732953717/2000000000000 : ℝ)*(major2) + (1189860150683817/25000000000000 : ℝ)*(sp0) + (297466174655439/6250000000000 : ℝ)*(sp1) + (2379729539601963/50000000000000 : ℝ)*(sp2) + (506125529776721/25000000000000 : ℝ)*(sp3) + (9816870061/50000000000000 : ℝ)*(sp4) + (10677873271/100000000000000 : ℝ)*(sp7) + (506128199245039/25000000000000 : ℝ)*(f.failure) + (475946023647539/10000000000000 : ℝ)*(f.sum) + (127529336534941/50430000000000000000000000000 : ℝ)*base65 + (38819438538778007417/5043000000000000000000000000000000 : ℝ)*base68 + (101741753617784713/33620000000000000000000000000000 : ℝ)*base69 + (25248801204520992583/5043000000000000000000000000000000 : ℝ)*base71 + (212559564863069/50430000000000000000000000000 : ℝ)*base74 + (32035132360535287/33620000000000000000000000000000 : ℝ)*base76 + (2021793669651030861/1681000000000000000000000000000000 : ℝ)*base77 + (4529138761861969139/1681000000000000000000000000000000 : ℝ)*base80 + (39826913723427/8405000000000000000000000000 : ℝ)*base81 + (380223/78125000000000000000 : ℝ)*base89 + (380223/78125000000000000000 : ℝ)*base91 + (401027/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243468598531367004440691851/52531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (579368909/100000000000000 : ℝ)*(base19) + (223732673/25000000000000 : ℝ)*(base23) + (104450793/100000000000000 : ℝ)*(upper3) + (77638871/100000000000000 : ℝ)*(lower4) + (28772359/50000000000000 : ℝ)*(upper5) + (428543506358753/12500000000000 : ℝ)*(major0) + (428543506358753/12500000000000 : ℝ)*(major1) + (428543506358753/12500000000000 : ℝ)*(major2) + (12742767691/100000000000000 : ℝ)*(sp1) + (8573246879/50000000000000 : ℝ)*(sp2) + (2405240393554219/50000000000000 : ℝ)*(sp4) + (2405233732485919/50000000000000 : ℝ)*(sp5) + (1202615686420997/25000000000000 : ℝ)*(sp6) + (511553790035081/25000000000000 : ℝ)*(sp7) + (511553790035081/25000000000000 : ℝ)*(f.failure) + (2405240393554219/50000000000000 : ℝ)*(f.sum) + (69563713853797/12607500000000000000000000000 : ℝ)*base66 + (4237090145549295649/630375000000000000000000000000000 : ℝ)*base68 + (2349898466178795649/630375000000000000000000000000000 : ℝ)*base70 + (13240586174479545649/630375000000000000000000000000000 : ℝ)*base72 + (8141915356961/6303750000000000000000000000 : ℝ)*base74 + (11605497819704351/630375000000000000000000000000000 : ℝ)*base75 + (7718750176386795649/630375000000000000000000000000000 : ℝ)*base78 + (7682043021567795649/630375000000000000000000000000000 : ℝ)*base80 + (32527680445387/12607500000000000000000000000 : ℝ)*base82 + (1095367/78125000000000000000 : ℝ)*base89 + (1095367/78125000000000000000 : ℝ)*base91 + (1095367/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1564_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7761/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1564_s4_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-896909017/5000000000 : ℝ)*x 0 + (5426729967/10000000000 : ℝ)*x 1 + (5219693609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896909017/5000000000 : ℝ)^4625 ≤ (2200942685991/20000000000000 : ℝ)^3601 := by
    have hnat : (896909017 : ℕ)^4625*20000000000000^3601 ≤ 2200942685991^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896909017 5000000000 2200942685991 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426729967/10000000000 : ℝ)^4625 ≤ (45608947441381/100000000000000 : ℝ)^3601 := by
    have hnat : (5426729967 : ℕ)^4625*100000000000000^3601 ≤ 45608947441381^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426729967 10000000000 45608947441381 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219693609/10000000000 : ℝ)^4625 ≤ (43386339115693/100000000000000 : ℝ)^3601 := by
    have hnat : (5219693609 : ℕ)^4625*100000000000000^3601 ≤ 43386339115693^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219693609 10000000000 43386339115693 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-896909017/5000000000 : ℝ), (5426729967/10000000000 : ℝ), (5219693609/10000000000 : ℝ)] ![(2200942685991/20000000000000 : ℝ), (45608947441381/100000000000000 : ℝ), (43386339115693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-896909017/5000000000 : ℝ)|^4625 ≤ (2200942685991/20000000000000 : ℝ)^3601
        have hw : |(-896909017/5000000000 : ℝ)|=(896909017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426729967/10000000000 : ℝ)|^4625 ≤ (45608947441381/100000000000000 : ℝ)^3601
        have hw : |(5426729967/10000000000 : ℝ)|=(5426729967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219693609/10000000000 : ℝ)|^4625 ≤ (43386339115693/100000000000000 : ℝ)^3601
        have hw : |(5219693609/10000000000 : ℝ)|=(5219693609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348604967/10000000000 : ℝ)*x 0 + (-1899750019/10000000000 : ℝ)*x 1 + (260984679/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348604967/10000000000 : ℝ)^4625 ≤ (44767363318969/100000000000000 : ℝ)^3601 := by
    have hnat : (5348604967 : ℕ)^4625*100000000000000^3601 ≤ 44767363318969^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348604967 10000000000 44767363318969 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899750019/10000000000 : ℝ)^4625 ≤ (5923148929289/50000000000000 : ℝ)^3601 := by
    have hnat : (1899750019 : ℕ)^4625*50000000000000^3601 ≤ 5923148929289^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899750019 10000000000 5923148929289 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260984679/500000000 : ℝ)^4625 ≤ (21693169403049/50000000000000 : ℝ)^3601 := by
    have hnat : (260984679 : ℕ)^4625*50000000000000^3601 ≤ 21693169403049^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260984679 500000000 21693169403049 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348604967/10000000000 : ℝ), (-1899750019/10000000000 : ℝ), (260984679/500000000 : ℝ)] ![(44767363318969/100000000000000 : ℝ), (5923148929289/50000000000000 : ℝ), (21693169403049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348604967/10000000000 : ℝ)|^4625 ≤ (44767363318969/100000000000000 : ℝ)^3601
        have hw : |(5348604967/10000000000 : ℝ)|=(5348604967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1899750019/10000000000 : ℝ)|^4625 ≤ (5923148929289/50000000000000 : ℝ)^3601
        have hw : |(-1899750019/10000000000 : ℝ)|=(1899750019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260984679/500000000 : ℝ)|^4625 ≤ (21693169403049/50000000000000 : ℝ)^3601
        have hw : |(260984679/500000000 : ℝ)|=(260984679/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069720981/2000000000 : ℝ)*x 0 + (1304923493/2500000000 : ℝ)*x 1 + (-94987479/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069720981/2000000000 : ℝ)^4625 ≤ (44767362652467/100000000000000 : ℝ)^3601 := by
    have hnat : (1069720981 : ℕ)^4625*100000000000000^3601 ≤ 44767362652467^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069720981 2000000000 44767362652467 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304923493/2500000000 : ℝ)^4625 ≤ (21693171495487/50000000000000 : ℝ)^3601 := by
    have hnat : (1304923493 : ℕ)^4625*50000000000000^3601 ≤ 21693171495487^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304923493 2500000000 21693171495487 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94987479/500000000 : ℝ)^4625 ≤ (2369258868531/20000000000000 : ℝ)^3601 := by
    have hnat : (94987479 : ℕ)^4625*20000000000000^3601 ≤ 2369258868531^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94987479 500000000 2369258868531 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069720981/2000000000 : ℝ), (1304923493/2500000000 : ℝ), (-94987479/500000000 : ℝ)] ![(44767362652467/100000000000000 : ℝ), (21693171495487/50000000000000 : ℝ), (2369258868531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069720981/2000000000 : ℝ)|^4625 ≤ (44767362652467/100000000000000 : ℝ)^3601
        have hw : |(1069720981/2000000000 : ℝ)|=(1069720981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304923493/2500000000 : ℝ)|^4625 ≤ (21693171495487/50000000000000 : ℝ)^3601
        have hw : |(1304923493/2500000000 : ℝ)|=(1304923493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94987479/500000000 : ℝ)|^4625 ≤ (2369258868531/20000000000000 : ℝ)^3601
        have hw : |(-94987479/500000000 : ℝ)|=(94987479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530767347/1250000000 : ℝ)*x 0 + (4008452219/10000000000 : ℝ)*x 1 + (4495175789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530767347/1250000000 : ℝ)^4625 ≤ (33281936012559/100000000000000 : ℝ)^3601 := by
    have hnat : (530767347 : ℕ)^4625*100000000000000^3601 ≤ 33281936012559^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530767347 1250000000 33281936012559 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4008452219/10000000000 : ℝ)^4625 ≤ (15454217056821/50000000000000 : ℝ)^3601 := by
    have hnat : (4008452219 : ℕ)^4625*50000000000000^3601 ≤ 15454217056821^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008452219 10000000000 15454217056821 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495175789/10000000000 : ℝ)^4625 ≤ (17904814927757/50000000000000 : ℝ)^3601 := by
    have hnat : (4495175789 : ℕ)^4625*50000000000000^3601 ≤ 17904814927757^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495175789 10000000000 17904814927757 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530767347/1250000000 : ℝ), (4008452219/10000000000 : ℝ), (4495175789/10000000000 : ℝ)] ![(33281936012559/100000000000000 : ℝ), (15454217056821/50000000000000 : ℝ), (17904814927757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530767347/1250000000 : ℝ)|^4625 ≤ (33281936012559/100000000000000 : ℝ)^3601
        have hw : |(530767347/1250000000 : ℝ)|=(530767347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4008452219/10000000000 : ℝ)|^4625 ≤ (15454217056821/50000000000000 : ℝ)^3601
        have hw : |(4008452219/10000000000 : ℝ)|=(4008452219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495175789/10000000000 : ℝ)|^4625 ≤ (17904814927757/50000000000000 : ℝ)^3601
        have hw : |(4495175789/10000000000 : ℝ)|=(4495175789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-896922597/5000000000 : ℝ)*x 0 + (652596589/1250000000 : ℝ)*x 1 + (2712821423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896922597/5000000000 : ℝ)^4625 ≤ (11004927432859/100000000000000 : ℝ)^3601 := by
    have hnat : (896922597 : ℕ)^4625*100000000000000^3601 ≤ 11004927432859^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896922597 5000000000 11004927432859 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652596589/1250000000 : ℝ)^4625 ≤ (21698929820417/50000000000000 : ℝ)^3601 := by
    have hnat : (652596589 : ℕ)^4625*50000000000000^3601 ≤ 21698929820417^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652596589 1250000000 21698929820417 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712821423/5000000000 : ℝ)^4625 ≤ (45597212904127/100000000000000 : ℝ)^3601 := by
    have hnat : (2712821423 : ℕ)^4625*100000000000000^3601 ≤ 45597212904127^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712821423 5000000000 45597212904127 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-896922597/5000000000 : ℝ), (652596589/1250000000 : ℝ), (2712821423/5000000000 : ℝ)] ![(11004927432859/100000000000000 : ℝ), (21698929820417/50000000000000 : ℝ), (45597212904127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-896922597/5000000000 : ℝ)|^4625 ≤ (11004927432859/100000000000000 : ℝ)^3601
        have hw : |(-896922597/5000000000 : ℝ)|=(896922597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652596589/1250000000 : ℝ)|^4625 ≤ (21698929820417/50000000000000 : ℝ)^3601
        have hw : |(652596589/1250000000 : ℝ)|=(652596589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712821423/5000000000 : ℝ)|^4625 ≤ (45597212904127/100000000000000 : ℝ)^3601
        have hw : |(2712821423/5000000000 : ℝ)|=(2712821423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293868853/10000000000 : ℝ)*x 0 + (-1693801219/10000000000 : ℝ)*x 1 + (2712821383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293868853/10000000000 : ℝ)^4625 ≤ (8835961363951/20000000000000 : ℝ)^3601 := by
    have hnat : (5293868853 : ℕ)^4625*20000000000000^3601 ≤ 8835961363951^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293868853 10000000000 8835961363951 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693801219/10000000000 : ℝ)^4625 ≤ (5111490563351/50000000000000 : ℝ)^3601 := by
    have hnat : (1693801219 : ℕ)^4625*50000000000000^3601 ≤ 5111490563351^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693801219 10000000000 5111490563351 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712821383/5000000000 : ℝ)^4625 ≤ (2279860602031/5000000000000 : ℝ)^3601 := by
    have hnat : (2712821383 : ℕ)^4625*5000000000000^3601 ≤ 2279860602031^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712821383 5000000000 2279860602031 5000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293868853/10000000000 : ℝ), (-1693801219/10000000000 : ℝ), (2712821383/5000000000 : ℝ)] ![(8835961363951/20000000000000 : ℝ), (5111490563351/50000000000000 : ℝ), (2279860602031/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293868853/10000000000 : ℝ)|^4625 ≤ (8835961363951/20000000000000 : ℝ)^3601
        have hw : |(5293868853/10000000000 : ℝ)|=(5293868853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1693801219/10000000000 : ℝ)|^4625 ≤ (5111490563351/50000000000000 : ℝ)^3601
        have hw : |(-1693801219/10000000000 : ℝ)|=(1693801219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712821383/5000000000 : ℝ)|^4625 ≤ (2279860602031/5000000000000 : ℝ)^3601
        have hw : |(2712821383/5000000000 : ℝ)|=(2712821383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646934279/5000000000 : ℝ)*x 0 + (217025719/400000000 : ℝ)*x 1 + (-211725167/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646934279/5000000000 : ℝ)^4625 ≤ (44179803657759/100000000000000 : ℝ)^3601 := by
    have hnat : (2646934279 : ℕ)^4625*100000000000000^3601 ≤ 44179803657759^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646934279 5000000000 44179803657759 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217025719/400000000 : ℝ)^4625 ≤ (45597214296531/100000000000000 : ℝ)^3601 := by
    have hnat : (217025719 : ℕ)^4625*100000000000000^3601 ≤ 45597214296531^3601*400000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217025719 400000000 45597214296531 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211725167/1250000000 : ℝ)^4625 ≤ (2044596406733/20000000000000 : ℝ)^3601 := by
    have hnat : (211725167 : ℕ)^4625*20000000000000^3601 ≤ 2044596406733^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211725167 1250000000 2044596406733 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646934279/5000000000 : ℝ), (217025719/400000000 : ℝ), (-211725167/1250000000 : ℝ)] ![(44179803657759/100000000000000 : ℝ), (45597214296531/100000000000000 : ℝ), (2044596406733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646934279/5000000000 : ℝ)|^4625 ≤ (44179803657759/100000000000000 : ℝ)^3601
        have hw : |(2646934279/5000000000 : ℝ)|=(2646934279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217025719/400000000 : ℝ)|^4625 ≤ (45597214296531/100000000000000 : ℝ)^3601
        have hw : |(217025719/400000000 : ℝ)|=(217025719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211725167/1250000000 : ℝ)|^4625 ≤ (2044596406733/20000000000000 : ℝ)^3601
        have hw : |(-211725167/1250000000 : ℝ)|=(211725167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s4_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246202377/10000000000 : ℝ)*x 0 + (4492640173/10000000000 : ℝ)*x 1 + (802201347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246202377/10000000000 : ℝ)^4625 ≤ (33282576289531/100000000000000 : ℝ)^3601 := by
    have hnat : (4246202377 : ℕ)^4625*100000000000000^3601 ≤ 33282576289531^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246202377 10000000000 33282576289531 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492640173/10000000000 : ℝ)^4625 ≤ (35783688634489/100000000000000 : ℝ)^3601 := by
    have hnat : (4492640173 : ℕ)^4625*100000000000000^3601 ≤ 35783688634489^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492640173 10000000000 35783688634489 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802201347/2000000000 : ℝ)^4625 ≤ (30933735066591/100000000000000 : ℝ)^3601 := by
    have hnat : (802201347 : ℕ)^4625*100000000000000^3601 ≤ 30933735066591^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802201347 2000000000 30933735066591 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246202377/10000000000 : ℝ), (4492640173/10000000000 : ℝ), (802201347/2000000000 : ℝ)] ![(33282576289531/100000000000000 : ℝ), (35783688634489/100000000000000 : ℝ), (30933735066591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246202377/10000000000 : ℝ)|^4625 ≤ (33282576289531/100000000000000 : ℝ)^3601
        have hw : |(4246202377/10000000000 : ℝ)|=(4246202377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492640173/10000000000 : ℝ)|^4625 ≤ (35783688634489/100000000000000 : ℝ)^3601
        have hw : |(4492640173/10000000000 : ℝ)|=(4492640173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802201347/2000000000 : ℝ)|^4625 ≤ (30933735066591/100000000000000 : ℝ)^3601
        have hw : |(802201347/2000000000 : ℝ)|=(802201347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7761/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5549/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7761/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7761/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7761/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7761/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7761/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7761/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11067/100000 : ℝ) ^ (4623/1024 : ℝ) ≤ (2416023370634441/50000000000000000000 : ℝ) := by
    have hpowers : (11067/100000 : ℝ)^4623 ≤ (2416023370634441/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11067 : ℕ)^4623*50000000000000000000^1024 ≤ 2416023370634441^1024*100000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11067 100000 2416023370634441 50000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11067/100000 : ℝ)) (X := (2416023370634441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7761/50000 : ℝ) ^ (4623/1024 : ℝ) ≤ (890170494125323/4000000000000000000 : ℝ) := by
    have hpowers : (7761/50000 : ℝ)^4623 ≤ (890170494125323/4000000000000000000 : ℝ)^1024 := by
      have hnat : (7761 : ℕ)^4623*4000000000000000000^1024 ≤ 890170494125323^1024*50000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7761 50000 890170494125323 4000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7761/50000 : ℝ)) (X := (890170494125323/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002416023370634441/25000000000000000000 : ℝ) ≤ (1250026756596053/1250000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (25002416023370634441/25000000000000000000 : ℝ)^1024 ≤ (1250026756596053/1250000000000000 : ℝ)^4623 := by
      have hnat : (25002416023370634441 : ℕ)^1024*1250000000000000^4623 ≤ 1250026756596053^4623*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002416023370634441 25000000000000000000 1250026756596053 1250000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026756596053/1250000000000000 : ℝ)) (X := (25002416023370634441/25000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027086309094401957/100000000000000000000 : ℝ) ≤ (500029995086139/500000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (100027086309094401957/100000000000000000000 : ℝ)^1024 ≤ (500029995086139/500000000000000 : ℝ)^4623 := by
      have hnat : (100027086309094401957 : ℕ)^1024*500000000000000^4623 ≤ 500029995086139^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027086309094401957 100000000000000000000 500029995086139 500000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500029995086139/500000000000000 : ℝ)) (X := (100027086309094401957/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000890170494125323/2000000000000000000 : ℝ) ≤ (625061609417321/625000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (2000890170494125323/2000000000000000000 : ℝ)^1024 ≤ (625061609417321/625000000000000 : ℝ)^4623 := by
      have hnat : (2000890170494125323 : ℕ)^1024*625000000000000^4623 ≤ 625061609417321^4623*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000890170494125323 2000000000000000000 625061609417321 625000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625061609417321/625000000000000 : ℝ)) (X := (2000890170494125323/2000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2416023370634441/50000000000000000000 : ℝ) ≤ ((463983471086745971/464062500000000000 : ℝ)+2*(96462238589/111375000000000 : ℝ)*(11067/100000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (463983471086745971/464062500000000000 : ℝ)+2*(96462238589/111375000000000 : ℝ)*(11067/100000 : ℝ)=(1250026756596053/1250000000000000 : ℝ) by norm_num, show 1+2*(2416023370634441/50000000000000000000 : ℝ)=(25002416023370634441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(890170494125323/4000000000000000000 : ℝ)+(2416023370634441/50000000000000000000 : ℝ) ≤ ((463983471086745971/464062500000000000 : ℝ)+(96462238589/111375000000000 : ℝ)*((7761/50000 : ℝ)+(11067/100000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (463983471086745971/464062500000000000 : ℝ)+(96462238589/111375000000000 : ℝ)*((7761/50000 : ℝ)+(11067/100000 : ℝ))=(500029995086139/500000000000000 : ℝ) by norm_num, show 1+(890170494125323/4000000000000000000 : ℝ)+(2416023370634441/50000000000000000000 : ℝ)=(100027086309094401957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(890170494125323/4000000000000000000 : ℝ) ≤ ((463983471086745971/464062500000000000 : ℝ)+2*(96462238589/111375000000000 : ℝ)*(7761/50000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (463983471086745971/464062500000000000 : ℝ)+2*(96462238589/111375000000000 : ℝ)*(7761/50000 : ℝ)=(625061609417321/625000000000000 : ℝ) by norm_num, show 1+2*(890170494125323/4000000000000000000 : ℝ)=(2000890170494125323/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (463983471086745971/464062500000000000 : ℝ)*(X 1 0+X 2 0)+(96462238589/111375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (7761/50000 : ℝ)) (c := (463983471086745971/464062500000000000 : ℝ)) (alpha := (96462238589/111375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (463983471086745971/464062500000000000 : ℝ)*(X 0 1+X 2 1)+(96462238589/111375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (7761/50000 : ℝ)) (c := (463983471086745971/464062500000000000 : ℝ)) (alpha := (96462238589/111375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (463983471086745971/464062500000000000 : ℝ)*(X 0 2+X 1 2)+(96462238589/111375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (7761/50000 : ℝ)) (c := (463983471086745971/464062500000000000 : ℝ)) (alpha := (96462238589/111375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-896909017/5000000000 : ℝ)*X 0 0+(5426729967/10000000000 : ℝ)*X 0 1+(5219693609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348604967/10000000000 : ℝ)*X 1 0+(-1899750019/10000000000 : ℝ)*X 1 1+(260984679/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069720981/2000000000 : ℝ)*X 2 0+(1304923493/2500000000 : ℝ)*X 2 1+(-94987479/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530767347/1250000000 : ℝ)*X 0 0+(4008452219/10000000000 : ℝ)*X 0 1+(4495175789/10000000000 : ℝ)*X 0 2+(530767347/1250000000 : ℝ)*X 1 0+(4008452219/10000000000 : ℝ)*X 1 1+(4495175789/10000000000 : ℝ)*X 1 2+(530767347/1250000000 : ℝ)*X 2 0+(4008452219/10000000000 : ℝ)*X 2 1+(4495175789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-896922597/5000000000 : ℝ)*X 0 0+(652596589/1250000000 : ℝ)*X 0 1+(2712821423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293868853/10000000000 : ℝ)*X 1 0+(-1693801219/10000000000 : ℝ)*X 1 1+(2712821383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646934279/5000000000 : ℝ)*X 2 0+(217025719/400000000 : ℝ)*X 2 1+(-211725167/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4246202377/10000000000 : ℝ)*X 0 0+(4492640173/10000000000 : ℝ)*X 0 1+(802201347/2000000000 : ℝ)*X 0 2+(4246202377/10000000000 : ℝ)*X 1 0+(4492640173/10000000000 : ℝ)*X 1 1+(802201347/2000000000 : ℝ)*X 1 2+(4246202377/10000000000 : ℝ)*X 2 0+(4492640173/10000000000 : ℝ)*X 2 1+(802201347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35049435402877505327123623/3867187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8267239/400000000000 : ℝ)*(base19) + (953933957/50000000000000 : ℝ)*(base23) + (11012957/20000000000000 : ℝ)*(lower2) + (2224913/25000000000000 : ℝ)*(upper3) + (91391727/25000000000000 : ℝ)*(upper5) + (1721183387074763/50000000000000 : ℝ)*(major0) + (1721183387074763/50000000000000 : ℝ)*(major1) + (1721183387074763/50000000000000 : ℝ)*(major2) + (4830104127414943/100000000000000 : ℝ)*(sp0) + (4830148921245023/100000000000000 : ℝ)*(sp1) + (2415074540093429/50000000000000 : ℝ)*(sp2) + (1027285003562487/50000000000000 : ℝ)*(sp3) + (4686063983/10000000000000 : ℝ)*(sp4) + (1531376211/12500000000000 : ℝ)*(sp7) + (1027291129067331/50000000000000 : ℝ)*(f.failure) + (4830150988054773/100000000000000 : ℝ)*(f.sum) + (46866590815903/11137500000000000000000000000 : ℝ)*base65 + (141635026114049497/34804687500000000000000000000000 : ℝ)*base67 + (42904657051975907/8701171875000000000000000000000 : ℝ)*base70 + (6041546010803629/1087646484375000000000000000000 : ℝ)*base72 + (112362949718681/22275000000000000000000000000 : ℝ)*base73 + (334166937184791631/69609375000000000000000000000000 : ℝ)*base76 + (50689940071041631/69609375000000000000000000000000 : ℝ)*base78 + (381405061268333369/69609375000000000000000000000000 : ℝ)*base79 + (54297798753197/11137500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (746117/156250000000000000000 : ℝ)*base89 + (746117/156250000000000000000 : ℝ)*base91 + (746117/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78939995559503532680589799/23203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99703087/50000000000000 : ℝ)*(base19) + (34522453/100000000000000 : ℝ)*(upper2) + (2389667/2000000000000 : ℝ)*(upper3) + (3908223/100000000000000 : ℝ)*(lower4) + (8914513/50000000000000 : ℝ)*(upper5) + (1739353544636991/50000000000000 : ℝ)*(major0) + (1739353544636991/50000000000000 : ℝ)*(major1) + (27177399134953/781250000000 : ℝ)*(major2) + (326861997/10000000000000 : ℝ)*(sp0) + (398752463/20000000000000 : ℝ)*(sp3) + (1220284690417987/25000000000000 : ℝ)*(sp4) + (4881141830885743/100000000000000 : ℝ)*(sp5) + (4881142030291917/100000000000000 : ℝ)*(sp6) + (1038135020544733/50000000000000 : ℝ)*(sp7) + (2076272034851781/100000000000000 : ℝ)*(f.failure) + (4881142030291917/100000000000000 : ℝ)*(f.sum) + (83261037776651/11137500000000000000000000000 : ℝ)*base66 + (589557559950739/543823242187500000000000000000 : ℝ)*base68 + (291260521423424857/23203125000000000000000000000000 : ℝ)*base69 + (172476005332720523/17402343750000000000000000000000 : ℝ)*base72 + (58435479620351/11137500000000000000000000000 : ℝ)*base74 + (394360604876549857/23203125000000000000000000000000 : ℝ)*base75 + (107355848993399239/23203125000000000000000000000000 : ℝ)*base78 + (41212719257382011/23203125000000000000000000000000 : ℝ)*base79 + (14585118419339/7425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5172267/312500000000000000000 : ℝ)*base89 + (5172267/312500000000000000000 : ℝ)*base91 + (1077733/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1564_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7761/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1564_s5_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1793843721/10000000000 : ℝ)*x 0 + (5426561933/10000000000 : ℝ)*x 1 + (652480569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793843721/10000000000 : ℝ)^4625 ≤ (5502457913283/50000000000000 : ℝ)^3601 := by
    have hnat : (1793843721 : ℕ)^4625*50000000000000^3601 ≤ 5502457913283^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793843721 10000000000 5502457913283 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426561933/10000000000 : ℝ)^4625 ≤ (11401783403757/25000000000000 : ℝ)^3601 := by
    have hnat : (5426561933 : ℕ)^4625*25000000000000^3601 ≤ 11401783403757^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426561933 10000000000 11401783403757 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652480569/1250000000 : ℝ)^4625 ≤ (43387950545431/100000000000000 : ℝ)^3601 := by
    have hnat : (652480569 : ℕ)^4625*100000000000000^3601 ≤ 43387950545431^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652480569 1250000000 43387950545431 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1793843721/10000000000 : ℝ), (5426561933/10000000000 : ℝ), (652480569/1250000000 : ℝ)] ![(5502457913283/50000000000000 : ℝ), (11401783403757/25000000000000 : ℝ), (43387950545431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1793843721/10000000000 : ℝ)|^4625 ≤ (5502457913283/50000000000000 : ℝ)^3601
        have hw : |(-1793843721/10000000000 : ℝ)|=(1793843721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426561933/10000000000 : ℝ)|^4625 ≤ (11401783403757/25000000000000 : ℝ)^3601
        have hw : |(5426561933/10000000000 : ℝ)|=(5426561933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652480569/1250000000 : ℝ)|^4625 ≤ (43387950545431/100000000000000 : ℝ)^3601
        have hw : |(652480569/1250000000 : ℝ)|=(652480569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348560017/10000000000 : ℝ)*x 0 + (-1899609279/10000000000 : ℝ)*x 1 + (208793777/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348560017/10000000000 : ℝ)^4625 ≤ (44766880105773/100000000000000 : ℝ)^3601 := by
    have hnat : (5348560017 : ℕ)^4625*100000000000000^3601 ≤ 44766880105773^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348560017 10000000000 44766880105773 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1899609279/10000000000 : ℝ)^4625 ≤ (5922585346421/50000000000000 : ℝ)^3601 := by
    have hnat : (1899609279 : ℕ)^4625*50000000000000^3601 ≤ 5922585346421^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899609279 10000000000 5922585346421 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208793777/400000000 : ℝ)^4625 ≤ (8677589837921/20000000000000 : ℝ)^3601 := by
    have hnat : (208793777 : ℕ)^4625*20000000000000^3601 ≤ 8677589837921^3601*400000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208793777 400000000 8677589837921 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348560017/10000000000 : ℝ), (-1899609279/10000000000 : ℝ), (208793777/400000000 : ℝ)] ![(44766880105773/100000000000000 : ℝ), (5922585346421/50000000000000 : ℝ), (8677589837921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348560017/10000000000 : ℝ)|^4625 ≤ (44766880105773/100000000000000 : ℝ)^3601
        have hw : |(5348560017/10000000000 : ℝ)|=(5348560017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1899609279/10000000000 : ℝ)|^4625 ≤ (5922585346421/50000000000000 : ℝ)^3601
        have hw : |(-1899609279/10000000000 : ℝ)|=(1899609279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208793777/400000000 : ℝ)|^4625 ≤ (8677589837921/20000000000000 : ℝ)^3601
        have hw : |(208793777/400000000 : ℝ)|=(208793777/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069712001/2000000000 : ℝ)*x 0 + (13049611/25000000 : ℝ)*x 1 + (-118725583/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069712001/2000000000 : ℝ)^4625 ≤ (44766879976773/100000000000000 : ℝ)^3601 := by
    have hnat : (1069712001 : ℕ)^4625*100000000000000^3601 ≤ 44766879976773^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069712001 2000000000 44766879976773 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13049611/25000000 : ℝ)^4625 ≤ (43387948922711/100000000000000 : ℝ)^3601 := by
    have hnat : (13049611 : ℕ)^4625*100000000000000^3601 ≤ 43387948922711^3601*25000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13049611 25000000 43387948922711 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118725583/625000000 : ℝ)^4625 ≤ (11845171085271/100000000000000 : ℝ)^3601 := by
    have hnat : (118725583 : ℕ)^4625*100000000000000^3601 ≤ 11845171085271^3601*625000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118725583 625000000 11845171085271 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069712001/2000000000 : ℝ), (13049611/25000000 : ℝ), (-118725583/625000000 : ℝ)] ![(44766879976773/100000000000000 : ℝ), (43387948922711/100000000000000 : ℝ), (11845171085271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069712001/2000000000 : ℝ)|^4625 ≤ (44766879976773/100000000000000 : ℝ)^3601
        have hw : |(1069712001/2000000000 : ℝ)|=(1069712001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13049611/25000000 : ℝ)|^4625 ≤ (43387948922711/100000000000000 : ℝ)^3601
        have hw : |(13049611/25000000 : ℝ)|=(13049611/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118725583/625000000 : ℝ)|^4625 ≤ (11845171085271/100000000000000 : ℝ)^3601
        have hw : |(-118725583/625000000 : ℝ)|=(118725583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4246154353/10000000000 : ℝ)*x 0 + (2004412069/5000000000 : ℝ)*x 1 + (224740023/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246154353/10000000000 : ℝ)^4625 ≤ (33282092827363/100000000000000 : ℝ)^3601 := by
    have hnat : (4246154353 : ℕ)^4625*100000000000000^3601 ≤ 33282092827363^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246154353 10000000000 33282092827363 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004412069/5000000000 : ℝ)^4625 ≤ (30912117463761/100000000000000 : ℝ)^3601 := by
    have hnat : (2004412069 : ℕ)^4625*100000000000000^3601 ≤ 30912117463761^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004412069 5000000000 30912117463761 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224740023/500000000 : ℝ)^4625 ≤ (35805789700697/100000000000000 : ℝ)^3601 := by
    have hnat : (224740023 : ℕ)^4625*100000000000000^3601 ≤ 35805789700697^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224740023 500000000 35805789700697 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4246154353/10000000000 : ℝ), (2004412069/5000000000 : ℝ), (224740023/500000000 : ℝ)] ![(33282092827363/100000000000000 : ℝ), (30912117463761/100000000000000 : ℝ), (35805789700697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4246154353/10000000000 : ℝ)|^4625 ≤ (33282092827363/100000000000000 : ℝ)^3601
        have hw : |(4246154353/10000000000 : ℝ)|=(4246154353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004412069/5000000000 : ℝ)|^4625 ≤ (30912117463761/100000000000000 : ℝ)^3601
        have hw : |(2004412069/5000000000 : ℝ)|=(2004412069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224740023/500000000 : ℝ)|^4625 ≤ (35805789700697/100000000000000 : ℝ)^3601
        have hw : |(224740023/500000000 : ℝ)|=(224740023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1793870729/10000000000 : ℝ)*x 0 + (32630749/62500000 : ℝ)*x 1 + (2712739339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793870729/10000000000 : ℝ)^4625 ≤ (440205145307/4000000000000 : ℝ)^3601 := by
    have hnat : (1793870729 : ℕ)^4625*4000000000000^3601 ≤ 440205145307^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793870729 10000000000 440205145307 4000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32630749/62500000 : ℝ)^4625 ≤ (21699715217377/50000000000000 : ℝ)^3601 := by
    have hnat : (32630749 : ℕ)^4625*50000000000000^3601 ≤ 21699715217377^3601*62500000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32630749 62500000 21699715217377 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712739339/5000000000 : ℝ)^4625 ≤ (22797720454853/50000000000000 : ℝ)^3601 := by
    have hnat : (2712739339 : ℕ)^4625*50000000000000^3601 ≤ 22797720454853^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712739339 5000000000 22797720454853 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1793870729/10000000000 : ℝ), (32630749/62500000 : ℝ), (2712739339/5000000000 : ℝ)] ![(440205145307/4000000000000 : ℝ), (21699715217377/50000000000000 : ℝ), (22797720454853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1793870729/10000000000 : ℝ)|^4625 ≤ (440205145307/4000000000000 : ℝ)^3601
        have hw : |(-1793870729/10000000000 : ℝ)|=(1793870729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32630749/62500000 : ℝ)|^4625 ≤ (21699715217377/50000000000000 : ℝ)^3601
        have hw : |(32630749/62500000 : ℝ)|=(32630749/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712739339/5000000000 : ℝ)|^4625 ≤ (22797720454853/50000000000000 : ℝ)^3601
        have hw : |(2712739339/5000000000 : ℝ)|=(2712739339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323477123/2500000000 : ℝ)*x 0 + (-211746861/1250000000 : ℝ)*x 1 + (5425478677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323477123/2500000000 : ℝ)^4625 ≤ (44180231695953/100000000000000 : ℝ)^3601 := by
    have hnat : (1323477123 : ℕ)^4625*100000000000000^3601 ≤ 44180231695953^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323477123 2500000000 44180231695953 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211746861/1250000000 : ℝ)^4625 ≤ (5112163698661/50000000000000 : ℝ)^3601 := by
    have hnat : (211746861 : ℕ)^4625*50000000000000^3601 ≤ 5112163698661^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211746861 1250000000 5112163698661 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425478677/10000000000 : ℝ)^4625 ≤ (1424857528091/3125000000000 : ℝ)^3601 := by
    have hnat : (5425478677 : ℕ)^4625*3125000000000^3601 ≤ 1424857528091^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425478677 10000000000 1424857528091 3125000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323477123/2500000000 : ℝ), (-211746861/1250000000 : ℝ), (5425478677/10000000000 : ℝ)] ![(44180231695953/100000000000000 : ℝ), (5112163698661/50000000000000 : ℝ), (1424857528091/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323477123/2500000000 : ℝ)|^4625 ≤ (44180231695953/100000000000000 : ℝ)^3601
        have hw : |(1323477123/2500000000 : ℝ)|=(1323477123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211746861/1250000000 : ℝ)|^4625 ≤ (5112163698661/50000000000000 : ℝ)^3601
        have hw : |(-211746861/1250000000 : ℝ)|=(211746861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425478677/10000000000 : ℝ)|^4625 ≤ (1424857528091/3125000000000 : ℝ)^3601
        have hw : |(5425478677/10000000000 : ℝ)|=(5425478677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293908499/10000000000 : ℝ)*x 0 + (2712739329/5000000000 : ℝ)*x 1 + (-211746863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293908499/10000000000 : ℝ)^4625 ≤ (5522528971373/12500000000000 : ℝ)^3601 := by
    have hnat : (5293908499 : ℕ)^4625*12500000000000^3601 ≤ 5522528971373^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293908499 10000000000 5522528971373 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712739329/5000000000 : ℝ)^4625 ≤ (45595440693831/100000000000000 : ℝ)^3601 := by
    have hnat : (2712739329 : ℕ)^4625*100000000000000^3601 ≤ 45595440693831^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712739329 5000000000 45595440693831 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211746863/1250000000 : ℝ)^4625 ≤ (2044865504271/20000000000000 : ℝ)^3601 := by
    have hnat : (211746863 : ℕ)^4625*20000000000000^3601 ≤ 2044865504271^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211746863 1250000000 2044865504271 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293908499/10000000000 : ℝ), (2712739329/5000000000 : ℝ), (-211746863/1250000000 : ℝ)] ![(5522528971373/12500000000000 : ℝ), (45595440693831/100000000000000 : ℝ), (2044865504271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293908499/10000000000 : ℝ)|^4625 ≤ (5522528971373/12500000000000 : ℝ)^3601
        have hw : |(5293908499/10000000000 : ℝ)|=(5293908499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712739329/5000000000 : ℝ)|^4625 ≤ (45595440693831/100000000000000 : ℝ)^3601
        have hw : |(2712739329/5000000000 : ℝ)|=(2712739329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211746863/1250000000 : ℝ)|^4625 ≤ (2044865504271/20000000000000 : ℝ)^3601
        have hw : |(-211746863/1250000000 : ℝ)|=(211746863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s5_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530777229/1250000000 : ℝ)*x 0 + (4492271911/10000000000 : ℝ)*x 1 + (1002842837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530777229/1250000000 : ℝ)^4625 ≤ (16641365938407/50000000000000 : ℝ)^3601 := by
    have hnat : (530777229 : ℕ)^4625*50000000000000^3601 ≤ 16641365938407^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530777229 1250000000 16641365938407 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492271911/10000000000 : ℝ)^4625 ≤ (17889960694457/50000000000000 : ℝ)^3601 := by
    have hnat : (4492271911 : ℕ)^4625*50000000000000^3601 ≤ 17889960694457^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492271911 10000000000 17889960694457 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002842837/2500000000 : ℝ)^4625 ≤ (1237493868561/4000000000000 : ℝ)^3601 := by
    have hnat : (1002842837 : ℕ)^4625*4000000000000^3601 ≤ 1237493868561^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002842837 2500000000 1237493868561 4000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530777229/1250000000 : ℝ), (4492271911/10000000000 : ℝ), (1002842837/2500000000 : ℝ)] ![(16641365938407/50000000000000 : ℝ), (17889960694457/50000000000000 : ℝ), (1237493868561/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530777229/1250000000 : ℝ)|^4625 ≤ (16641365938407/50000000000000 : ℝ)^3601
        have hw : |(530777229/1250000000 : ℝ)|=(530777229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492271911/10000000000 : ℝ)|^4625 ≤ (17889960694457/50000000000000 : ℝ)^3601
        have hw : |(4492271911/10000000000 : ℝ)|=(4492271911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002842837/2500000000 : ℝ)|^4625 ≤ (1237493868561/4000000000000 : ℝ)^3601
        have hw : |(1002842837/2500000000 : ℝ)|=(1002842837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5549/50000 : ℝ) ^ (4623/1024 : ℝ) ≤ (2446727332066503/50000000000000000000 : ℝ) := by
    have hpowers : (5549/50000 : ℝ)^4623 ≤ (2446727332066503/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5549 : ℕ)^4623*50000000000000000000^1024 ≤ 2446727332066503^1024*50000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5549 50000 2446727332066503 50000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5549/50000 : ℝ)) (X := (2446727332066503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4623/1024 : ℝ) ≤ (137718963210479/625000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4623 ≤ (137718963210479/625000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4623*625000000000000000^1024 ≤ 137718963210479^1024*3125^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 137718963210479 625000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (137718963210479/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002446727332066503/25000000000000000000 : ℝ) ≤ (10000216772948067/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (25002446727332066503/25000000000000000000 : ℝ)^1024 ≤ (10000216772948067/10000000000000000 : ℝ)^4623 := by
      have hnat : (25002446727332066503 : ℕ)^1024*10000000000000000^4623 ≤ 10000216772948067^4623*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002446727332066503 25000000000000000000 10000216772948067 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000216772948067/10000000000000000 : ℝ)) (X := (25002446727332066503/25000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013464244388904823/50000000000000000000 : ℝ) ≤ (10000596406718803/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (50013464244388904823/50000000000000000000 : ℝ)^1024 ≤ (10000596406718803/10000000000000000 : ℝ)^4623 := by
      have hnat : (50013464244388904823 : ℕ)^1024*10000000000000000^4623 ≤ 10000596406718803^4623*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013464244388904823 50000000000000000000 10000596406718803 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000596406718803/10000000000000000 : ℝ)) (X := (50013464244388904823/50000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312637718963210479/312500000000000000 : ℝ) ≤ (10000976040489539/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (312637718963210479/312500000000000000 : ℝ)^1024 ≤ (10000976040489539/10000000000000000 : ℝ)^4623 := by
      have hnat : (312637718963210479 : ℕ)^1024*10000000000000000^4623 ≤ 10000976040489539^4623*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312637718963210479 312500000000000000 10000976040489539 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000976040489539/10000000000000000 : ℝ)) (X := (312637718963210479/312500000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2446727332066503/50000000000000000000 : ℝ) ≤ ((21946262641033378937/21950000000000000000 : ℝ)+2*(23727110671/27437500000000 : ℝ)*(5549/50000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (21946262641033378937/21950000000000000000 : ℝ)+2*(23727110671/27437500000000 : ℝ)*(5549/50000 : ℝ)=(10000216772948067/10000000000000000 : ℝ) by norm_num, show 1+2*(2446727332066503/50000000000000000000 : ℝ)=(25002446727332066503/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137718963210479/625000000000000000 : ℝ)+(2446727332066503/50000000000000000000 : ℝ) ≤ ((21946262641033378937/21950000000000000000 : ℝ)+(23727110671/27437500000000 : ℝ)*((484/3125 : ℝ)+(5549/50000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (21946262641033378937/21950000000000000000 : ℝ)+(23727110671/27437500000000 : ℝ)*((484/3125 : ℝ)+(5549/50000 : ℝ))=(10000596406718803/10000000000000000 : ℝ) by norm_num, show 1+(137718963210479/625000000000000000 : ℝ)+(2446727332066503/50000000000000000000 : ℝ)=(50013464244388904823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137718963210479/625000000000000000 : ℝ) ≤ ((21946262641033378937/21950000000000000000 : ℝ)+2*(23727110671/27437500000000 : ℝ)*(484/3125 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (21946262641033378937/21950000000000000000 : ℝ)+2*(23727110671/27437500000000 : ℝ)*(484/3125 : ℝ)=(10000976040489539/10000000000000000 : ℝ) by norm_num, show 1+2*(137718963210479/625000000000000000 : ℝ)=(312637718963210479/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21946262641033378937/21950000000000000000 : ℝ)*(X 1 0+X 2 0)+(23727110671/27437500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (21946262641033378937/21950000000000000000 : ℝ)) (alpha := (23727110671/27437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21946262641033378937/21950000000000000000 : ℝ)*(X 0 1+X 2 1)+(23727110671/27437500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (21946262641033378937/21950000000000000000 : ℝ)) (alpha := (23727110671/27437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21946262641033378937/21950000000000000000 : ℝ)*(X 0 2+X 1 2)+(23727110671/27437500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (21946262641033378937/21950000000000000000 : ℝ)) (alpha := (23727110671/27437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1793843721/10000000000 : ℝ)*X 0 0+(5426561933/10000000000 : ℝ)*X 0 1+(652480569/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348560017/10000000000 : ℝ)*X 1 0+(-1899609279/10000000000 : ℝ)*X 1 1+(208793777/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069712001/2000000000 : ℝ)*X 2 0+(13049611/25000000 : ℝ)*X 2 1+(-118725583/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4246154353/10000000000 : ℝ)*X 0 0+(2004412069/5000000000 : ℝ)*X 0 1+(224740023/500000000 : ℝ)*X 0 2+(4246154353/10000000000 : ℝ)*X 1 0+(2004412069/5000000000 : ℝ)*X 1 1+(224740023/500000000 : ℝ)*X 1 2+(4246154353/10000000000 : ℝ)*X 2 0+(2004412069/5000000000 : ℝ)*X 2 1+(224740023/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1793870729/10000000000 : ℝ)*X 0 0+(32630749/62500000 : ℝ)*X 0 1+(2712739339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323477123/2500000000 : ℝ)*X 1 0+(-211746861/1250000000 : ℝ)*X 1 1+(5425478677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293908499/10000000000 : ℝ)*X 2 0+(2712739329/5000000000 : ℝ)*X 2 1+(-211746863/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530777229/1250000000 : ℝ)*X 0 0+(4492271911/10000000000 : ℝ)*X 0 1+(1002842837/2500000000 : ℝ)*X 0 2+(530777229/1250000000 : ℝ)*X 1 0+(4492271911/10000000000 : ℝ)*X 1 1+(1002842837/2500000000 : ℝ)*X 1 2+(530777229/1250000000 : ℝ)*X 2 0+(4492271911/10000000000 : ℝ)*X 2 1+(1002842837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14277250843982235419142663189/1097500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1976250987/100000000000000 : ℝ)*(base19) + (931869547/50000000000000 : ℝ)*(base23) + (54372567/100000000000000 : ℝ)*(lower2) + (162279103/50000000000000 : ℝ)*(upper3) + (100205607/50000000000000 : ℝ)*(upper5) + (3447661014465689/100000000000000 : ℝ)*(major0) + (3447661014465689/100000000000000 : ℝ)*(major1) + (344766101446569/10000000000000 : ℝ)*(major2) + (604694036543277/12500000000000 : ℝ)*(sp0) + (1209394371223899/25000000000000 : ℝ)*(sp1) + (18896787489873/390625000000 : ℝ)*(sp2) + (411545376870629/20000000000000 : ℝ)*(sp3) + (13584400183/50000000000000 : ℝ)*(sp4) + (15249802159/100000000000000 : ℝ)*(sp7) + (257217766769413/12500000000000 : ℝ)*(f.failure) + (2418789730573291/50000000000000 : ℝ)*(f.sum) + (29886050751311/10975000000000000000000000000 : ℝ)*base65 + (6686423372448792593/2195000000000000000000000000000000 : ℝ)*base67 + (2902269519587037153/219500000000000000000000000000000 : ℝ)*base69 + (3858681000261207407/2195000000000000000000000000000000 : ℝ)*base72 + (17155691120611/10975000000000000000000000000 : ℝ)*base73 + (920043837647037153/219500000000000000000000000000000 : ℝ)*base75 + (16651097104858007407/2195000000000000000000000000000000 : ℝ)*base78 + (10681860775328007407/2195000000000000000000000000000000 : ℝ)*base80 + (695546685297/685937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (102833/19531250000000000000 : ℝ)*base89 + (102833/19531250000000000000 : ℝ)*base91 + (184959/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4211147419589898254663533251/548750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263827423/20000000000000 : ℝ)*(base19) + (169570919/12500000000000 : ℝ)*(base23) + (11154961/2500000000000 : ℝ)*(lower1) + (73139373/50000000000000 : ℝ)*(upper3) + (19177467/100000000000000 : ℝ)*(lower4) + (176069781/100000000000000 : ℝ)*(upper5) + (3483985140815959/100000000000000 : ℝ)*(major0) + (3483985140815959/100000000000000 : ℝ)*(major1) + (3483985140815959/100000000000000 : ℝ)*(major2) + (254725179/50000000000000 : ℝ)*(sp1) + (977709555450701/20000000000000 : ℝ)*(sp4) + (4888545948666033/100000000000000 : ℝ)*(sp5) + (4888546420686153/100000000000000 : ℝ)*(sp6) + (2079422248575983/100000000000000 : ℝ)*(sp7) + (2079422248575983/100000000000000 : ℝ)*(f.failure) + (977709555450701/20000000000000 : ℝ)*(f.sum) + (34380888490313/10975000000000000000000000000 : ℝ)*base66 + (1661681544780255583/2195000000000000000000000000000000 : ℝ)*base67 + (20297563514385255583/2195000000000000000000000000000000 : ℝ)*base69 + (9102809544105255583/2195000000000000000000000000000000 : ℝ)*base71 + (66685676050913/10975000000000000000000000000 : ℝ)*base74 + (12359572077309744417/2195000000000000000000000000000000 : ℝ)*base76 + (6551064919230255583/2195000000000000000000000000000000 : ℝ)*base77 + (6373065819350255583/2195000000000000000000000000000000 : ℝ)*base79 + (15068367566303/2743750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (51719/312500000000000000000 : ℝ)*base90 + (51719/312500000000000000000 : ℝ)*base92 + (51719/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1564_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1564_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1564_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1564_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1564_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
