-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:50:02.653176+00:00
-- url     : https://prove2.me/submissions/9b20b585-af07-4e90-bbc8-2c231183190b

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
theorem support_rectangle_w1045_s0_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-961447637/5000000000 : ℝ)*x 0 + (6077022339/10000000000 : ℝ)*x 1 + (4768082567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961447637/5000000000 : ℝ)^4119 ≤ (11144174384403/100000000000000 : ℝ)^3095 := by
    have hnat : (961447637 : ℕ)^4119*100000000000000^3095 ≤ 11144174384403^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961447637 5000000000 11144174384403 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6077022339/10000000000 : ℝ)^4119 ≤ (51537529863409/100000000000000 : ℝ)^3095 := by
    have hnat : (6077022339 : ℕ)^4119*100000000000000^3095 ≤ 51537529863409^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6077022339 10000000000 51537529863409 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4768082567/10000000000 : ℝ)^4119 ≤ (18659147871463/50000000000000 : ℝ)^3095 := by
    have hnat : (4768082567 : ℕ)^4119*50000000000000^3095 ≤ 18659147871463^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768082567 10000000000 18659147871463 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961447637/5000000000 : ℝ), (6077022339/10000000000 : ℝ), (4768082567/10000000000 : ℝ)] ![(11144174384403/100000000000000 : ℝ), (51537529863409/100000000000000 : ℝ), (18659147871463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961447637/5000000000 : ℝ)|^4119 ≤ (11144174384403/100000000000000 : ℝ)^3095
        have hw : |(-961447637/5000000000 : ℝ)|=(961447637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6077022339/10000000000 : ℝ)|^4119 ≤ (51537529863409/100000000000000 : ℝ)^3095
        have hw : |(6077022339/10000000000 : ℝ)|=(6077022339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4768082567/10000000000 : ℝ)|^4119 ≤ (18659147871463/50000000000000 : ℝ)^3095
        have hw : |(4768082567/10000000000 : ℝ)|=(4768082567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5522254391/10000000000 : ℝ)*x 0 + (-1338479451/5000000000 : ℝ)*x 1 + (476808359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522254391/10000000000 : ℝ)^4119 ≤ (9074527370223/20000000000000 : ℝ)^3095 := by
    have hnat : (5522254391 : ℕ)^4119*20000000000000^3095 ≤ 9074527370223^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522254391 10000000000 9074527370223 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338479451/5000000000 : ℝ)^4119 ≤ (17309056737761/100000000000000 : ℝ)^3095 := by
    have hnat : (1338479451 : ℕ)^4119*100000000000000^3095 ≤ 17309056737761^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338479451 5000000000 17309056737761 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476808359/1000000000 : ℝ)^4119 ≤ (4664788299837/12500000000000 : ℝ)^3095 := by
    have hnat : (476808359 : ℕ)^4119*12500000000000^3095 ≤ 4664788299837^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476808359 1000000000 4664788299837 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522254391/10000000000 : ℝ), (-1338479451/5000000000 : ℝ), (476808359/1000000000 : ℝ)] ![(9074527370223/20000000000000 : ℝ), (17309056737761/100000000000000 : ℝ), (4664788299837/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522254391/10000000000 : ℝ)|^4119 ≤ (9074527370223/20000000000000 : ℝ)^3095
        have hw : |(5522254391/10000000000 : ℝ)|=(5522254391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338479451/5000000000 : ℝ)|^4119 ≤ (17309056737761/100000000000000 : ℝ)^3095
        have hw : |(-1338479451/5000000000 : ℝ)|=(1338479451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(476808359/1000000000 : ℝ)|^4119 ≤ (4664788299837/12500000000000 : ℝ)^3095
        have hw : |(476808359/1000000000 : ℝ)|=(476808359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5522254661/10000000000 : ℝ)*x 0 + (2384041441/5000000000 : ℝ)*x 1 + (-334619927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522254661/10000000000 : ℝ)^4119 ≤ (45372639803497/100000000000000 : ℝ)^3095 := by
    have hnat : (5522254661 : ℕ)^4119*100000000000000^3095 ≤ 45372639803497^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522254661 10000000000 45372639803497 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384041441/5000000000 : ℝ)^4119 ≤ (9329574756007/25000000000000 : ℝ)^3095 := by
    have hnat : (2384041441 : ℕ)^4119*25000000000000^3095 ≤ 9329574756007^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384041441 5000000000 9329574756007 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334619927/1250000000 : ℝ)^4119 ≤ (17309061160853/100000000000000 : ℝ)^3095 := by
    have hnat : (334619927 : ℕ)^4119*100000000000000^3095 ≤ 17309061160853^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334619927 1250000000 17309061160853 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522254661/10000000000 : ℝ), (2384041441/5000000000 : ℝ), (-334619927/1250000000 : ℝ)] ![(45372639803497/100000000000000 : ℝ), (9329574756007/25000000000000 : ℝ), (17309061160853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522254661/10000000000 : ℝ)|^4119 ≤ (45372639803497/100000000000000 : ℝ)^3095
        have hw : |(5522254661/10000000000 : ℝ)|=(5522254661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2384041441/5000000000 : ℝ)|^4119 ≤ (9329574756007/25000000000000 : ℝ)^3095
        have hw : |(2384041441/5000000000 : ℝ)|=(2384041441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334619927/1250000000 : ℝ)|^4119 ≤ (17309061160853/100000000000000 : ℝ)^3095
        have hw : |(-334619927/1250000000 : ℝ)|=(334619927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (841790787/2000000000 : ℝ)*x 0 + (3126010119/10000000000 : ℝ)*x 1 + (5680655803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841790787/2000000000 : ℝ)^4119 ≤ (1580519521979/5000000000000 : ℝ)^3095 := by
    have hnat : (841790787 : ℕ)^4119*5000000000000^3095 ≤ 1580519521979^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841790787 2000000000 1580519521979 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3126010119/10000000000 : ℝ)^4119 ≤ (21276726232841/100000000000000 : ℝ)^3095 := by
    have hnat : (3126010119 : ℕ)^4119*100000000000000^3095 ≤ 21276726232841^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126010119 10000000000 21276726232841 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680655803/10000000000 : ℝ)^4119 ≤ (47112883303273/100000000000000 : ℝ)^3095 := by
    have hnat : (5680655803 : ℕ)^4119*100000000000000^3095 ≤ 47112883303273^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680655803 10000000000 47112883303273 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841790787/2000000000 : ℝ), (3126010119/10000000000 : ℝ), (5680655803/10000000000 : ℝ)] ![(1580519521979/5000000000000 : ℝ), (21276726232841/100000000000000 : ℝ), (47112883303273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841790787/2000000000 : ℝ)|^4119 ≤ (1580519521979/5000000000000 : ℝ)^3095
        have hw : |(841790787/2000000000 : ℝ)|=(841790787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3126010119/10000000000 : ℝ)|^4119 ≤ (21276726232841/100000000000000 : ℝ)^3095
        have hw : |(3126010119/10000000000 : ℝ)|=(3126010119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680655803/10000000000 : ℝ)|^4119 ≤ (47112883303273/100000000000000 : ℝ)^3095
        have hw : |(5680655803/10000000000 : ℝ)|=(5680655803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928332503/10000000000 : ℝ)*x 0 + (2400944981/5000000000 : ℝ)*x 1 + (755254357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928332503/10000000000 : ℝ)^4119 ≤ (5593065671753/50000000000000 : ℝ)^3095 := by
    have hnat : (1928332503 : ℕ)^4119*50000000000000^3095 ≤ 5593065671753^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928332503 10000000000 5593065671753 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400944981/5000000000 : ℝ)^4119 ≤ (18835426307141/50000000000000 : ℝ)^3095 := by
    have hnat : (2400944981 : ℕ)^4119*50000000000000^3095 ≤ 18835426307141^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400944981 5000000000 18835426307141 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755254357/1250000000 : ℝ)^4119 ≤ (25571508012163/50000000000000 : ℝ)^3095 := by
    have hnat : (755254357 : ℕ)^4119*50000000000000^3095 ≤ 25571508012163^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755254357 1250000000 25571508012163 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928332503/10000000000 : ℝ), (2400944981/5000000000 : ℝ), (755254357/1250000000 : ℝ)] ![(5593065671753/50000000000000 : ℝ), (18835426307141/50000000000000 : ℝ), (25571508012163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928332503/10000000000 : ℝ)|^4119 ≤ (5593065671753/50000000000000 : ℝ)^3095
        have hw : |(-1928332503/10000000000 : ℝ)|=(1928332503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400944981/5000000000 : ℝ)|^4119 ≤ (18835426307141/50000000000000 : ℝ)^3095
        have hw : |(2400944981/5000000000 : ℝ)|=(2400944981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755254357/1250000000 : ℝ)|^4119 ≤ (25571508012163/50000000000000 : ℝ)^3095
        have hw : |(755254357/1250000000 : ℝ)|=(755254357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5167107147/10000000000 : ℝ)*x 0 + (-140300599/1000000000 : ℝ)*x 1 + (604203513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167107147/10000000000 : ℝ)^4119 ≤ (41531116669243/100000000000000 : ℝ)^3095 := by
    have hnat : (5167107147 : ℕ)^4119*100000000000000^3095 ≤ 41531116669243^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167107147 10000000000 41531116669243 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140300599/1000000000 : ℝ)^4119 ≤ (1465172840763/20000000000000 : ℝ)^3095 := by
    have hnat : (140300599 : ℕ)^4119*20000000000000^3095 ≤ 1465172840763^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140300599 1000000000 1465172840763 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604203513/1000000000 : ℝ)^4119 ≤ (51143019110957/100000000000000 : ℝ)^3095 := by
    have hnat : (604203513 : ℕ)^4119*100000000000000^3095 ≤ 51143019110957^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604203513 1000000000 51143019110957 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167107147/10000000000 : ℝ), (-140300599/1000000000 : ℝ), (604203513/1000000000 : ℝ)] ![(41531116669243/100000000000000 : ℝ), (1465172840763/20000000000000 : ℝ), (51143019110957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167107147/10000000000 : ℝ)|^4119 ≤ (41531116669243/100000000000000 : ℝ)^3095
        have hw : |(5167107147/10000000000 : ℝ)|=(5167107147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140300599/1000000000 : ℝ)|^4119 ≤ (1465172840763/20000000000000 : ℝ)^3095
        have hw : |(-140300599/1000000000 : ℝ)|=(140300599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604203513/1000000000 : ℝ)|^4119 ≤ (51143019110957/100000000000000 : ℝ)^3095
        have hw : |(604203513/1000000000 : ℝ)|=(604203513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5167104763/10000000000 : ℝ)*x 0 + (3021018673/5000000000 : ℝ)*x 1 + (-1403006067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167104763/10000000000 : ℝ)^4119 ≤ (20765545583937/50000000000000 : ℝ)^3095 := by
    have hnat : (5167104763 : ℕ)^4119*50000000000000^3095 ≤ 20765545583937^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167104763 10000000000 20765545583937 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021018673/5000000000 : ℝ)^4119 ≤ (81828870519/160000000000 : ℝ)^3095 := by
    have hnat : (3021018673 : ℕ)^4119*160000000000^3095 ≤ 81828870519^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021018673 5000000000 81828870519 160000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403006067/10000000000 : ℝ)^4119 ≤ (3662932369449/50000000000000 : ℝ)^3095 := by
    have hnat : (1403006067 : ℕ)^4119*50000000000000^3095 ≤ 3662932369449^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403006067 10000000000 3662932369449 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167104763/10000000000 : ℝ), (3021018673/5000000000 : ℝ), (-1403006067/10000000000 : ℝ)] ![(20765545583937/50000000000000 : ℝ), (81828870519/160000000000 : ℝ), (3662932369449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167104763/10000000000 : ℝ)|^4119 ≤ (20765545583937/50000000000000 : ℝ)^3095
        have hw : |(5167104763/10000000000 : ℝ)|=(5167104763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021018673/5000000000 : ℝ)|^4119 ≤ (81828870519/160000000000 : ℝ)^3095
        have hw : |(3021018673/5000000000 : ℝ)|=(3021018673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1403006067/10000000000 : ℝ)|^4119 ≤ (3662932369449/50000000000000 : ℝ)^3095
        have hw : |(-1403006067/10000000000 : ℝ)|=(1403006067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s0_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219563083/10000000000 : ℝ)*x 0 + (5614678493/10000000000 : ℝ)*x 1 + (1597146029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219563083/10000000000 : ℝ)^4119 ≤ (31716474048767/100000000000000 : ℝ)^3095 := by
    have hnat : (4219563083 : ℕ)^4119*100000000000000^3095 ≤ 31716474048767^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219563083 10000000000 31716474048767 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5614678493/10000000000 : ℝ)^4119 ≤ (23193029414601/50000000000000 : ℝ)^3095 := by
    have hnat : (5614678493 : ℕ)^4119*50000000000000^3095 ≤ 23193029414601^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614678493 10000000000 23193029414601 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1597146029/5000000000 : ℝ)^4119 ≤ (1368591694139/6250000000000 : ℝ)^3095 := by
    have hnat : (1597146029 : ℕ)^4119*6250000000000^3095 ≤ 1368591694139^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597146029 5000000000 1368591694139 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219563083/10000000000 : ℝ), (5614678493/10000000000 : ℝ), (1597146029/5000000000 : ℝ)] ![(31716474048767/100000000000000 : ℝ), (23193029414601/50000000000000 : ℝ), (1368591694139/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219563083/10000000000 : ℝ)|^4119 ≤ (31716474048767/100000000000000 : ℝ)^3095
        have hw : |(4219563083/10000000000 : ℝ)|=(4219563083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5614678493/10000000000 : ℝ)|^4119 ≤ (23193029414601/50000000000000 : ℝ)^3095
        have hw : |(5614678493/10000000000 : ℝ)|=(5614678493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1597146029/5000000000 : ℝ)|^4119 ≤ (1368591694139/6250000000000 : ℝ)^3095
        have hw : |(1597146029/5000000000 : ℝ)|=(1597146029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28191/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8237/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8237 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8237*1^2048 ≤ 0^2048*1^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8237/2048 : ℝ) ≤ (1254487015779750179/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8237 ≤ (1254487015779750179/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8237*50000000000000000000^2048 ≤ 1254487015779750179^2048*5^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1254487015779750179 50000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1254487015779750179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8237 := by
      have hnat : (1 : ℕ)^2048*1^8237 ≤ 1^8237*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51254487015779750179/50000000000000000000 : ℝ) ≤ (2515450537047491/2500000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (51254487015779750179/50000000000000000000 : ℝ)^2048 ≤ (2515450537047491/2500000000000000 : ℝ)^8237 := by
      have hnat : (51254487015779750179 : ℕ)^2048*2500000000000000^8237 ≤ 2515450537047491^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51254487015779750179 50000000000000000000 2515450537047491 2500000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515450537047491/2500000000000000 : ℝ)) (X := (51254487015779750179/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26254487015779750179/25000000000000000000 : ℝ) ≤ (1265450537047491/1250000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (26254487015779750179/25000000000000000000 : ℝ)^2048 ≤ (1265450537047491/1250000000000000 : ℝ)^8237 := by
      have hnat : (26254487015779750179 : ℕ)^2048*1250000000000000^8237 ≤ 1265450537047491^8237*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26254487015779750179 25000000000000000000 1265450537047491 1250000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265450537047491/1250000000000000 : ℝ)) (X := (26254487015779750179/25000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15450537047491/1000000000000000 : ℝ)*(0 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15450537047491/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1254487015779750179/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15450537047491/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15450537047491/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515450537047491/2500000000000000 : ℝ) by norm_num, show 1+(1254487015779750179/50000000000000000000 : ℝ)+(0 : ℝ)=(51254487015779750179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1254487015779750179/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15450537047491/1000000000000000 : ℝ)*(2/5 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15450537047491/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265450537047491/1250000000000000 : ℝ) by norm_num, show 1+2*(1254487015779750179/50000000000000000000 : ℝ)=(26254487015779750179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15450537047491/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15450537047491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15450537047491/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15450537047491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15450537047491/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15450537047491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-961447637/5000000000 : ℝ)*X 0 0+(6077022339/10000000000 : ℝ)*X 0 1+(4768082567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5522254391/10000000000 : ℝ)*X 1 0+(-1338479451/5000000000 : ℝ)*X 1 1+(476808359/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5522254661/10000000000 : ℝ)*X 2 0+(2384041441/5000000000 : ℝ)*X 2 1+(-334619927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841790787/2000000000 : ℝ)*X 0 0+(3126010119/10000000000 : ℝ)*X 0 1+(5680655803/10000000000 : ℝ)*X 0 2+(841790787/2000000000 : ℝ)*X 1 0+(3126010119/10000000000 : ℝ)*X 1 1+(5680655803/10000000000 : ℝ)*X 1 2+(841790787/2000000000 : ℝ)*X 2 0+(3126010119/10000000000 : ℝ)*X 2 1+(5680655803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1928332503/10000000000 : ℝ)*X 0 0+(2400944981/5000000000 : ℝ)*X 0 1+(755254357/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167107147/10000000000 : ℝ)*X 1 0+(-140300599/1000000000 : ℝ)*X 1 1+(604203513/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5167104763/10000000000 : ℝ)*X 2 0+(3021018673/5000000000 : ℝ)*X 2 1+(-1403006067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4219563083/10000000000 : ℝ)*X 0 0+(5614678493/10000000000 : ℝ)*X 0 1+(1597146029/5000000000 : ℝ)*X 0 2+(4219563083/10000000000 : ℝ)*X 1 0+(5614678493/10000000000 : ℝ)*X 1 1+(1597146029/5000000000 : ℝ)*X 1 2+(4219563083/10000000000 : ℝ)*X 2 0+(5614678493/10000000000 : ℝ)*X 2 1+(1597146029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17028766899371560167933/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1852827909/100000000000000 : ℝ)*(base19) + (180086317/10000000000000 : ℝ)*(base23) + (104484343/100000000000000 : ℝ)*(base24) + (15602477/100000000000000 : ℝ)*(base39) + (91123881/20000000000000 : ℝ)*(upper3) + (57771905117979/10000000000000 : ℝ)*(major0) + (57771905117979/10000000000000 : ℝ)*(major1) + (577719035577313/100000000000000 : ℝ)*(major2) + (76398402793439/10000000000000 : ℝ)*(sp0) + (190996705359977/25000000000000 : ℝ)*(sp1) + (763986784522781/100000000000000 : ℝ)*(sp2) + (391445730755113/100000000000000 : ℝ)*(sp3) + (1161583357/25000000000000 : ℝ)*(sp4) + (431835493/12500000000000 : ℝ)*(sp7) + (391449185439057/100000000000000 : ℝ)*(f.failure) + (381994344935147/50000000000000 : ℝ)*(f.sum) + (198384906278573/100000000000000000000000000000 : ℝ)*base65 + (885693595328317/100000000000000000000000000000 : ℝ)*base68 + (29376351050689/10000000000000000000000000000 : ℝ)*base69 + (135773820328317/100000000000000000000000000000 : ℝ)*base72 + (34138110278573/100000000000000000000000000000 : ℝ)*base73 + (79844708830689/10000000000000000000000000000 : ℝ)*base75 + (108231539311/10000000000000000000000000000 : ℝ)*base78 + (9182715869311/10000000000000000000000000000 : ℝ)*base80 + (10499522965689/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (259449/5000000000000000000000 : ℝ)*base90 + (259449/5000000000000000000000 : ℝ)*base92 + (259449/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14829594728022927774507/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62925091/12500000000000 : ℝ)*(base19) + (312307799/50000000000000 : ℝ)*(base23) + (5448849/1250000000000 : ℝ)*(base39) + (156414359/100000000000000 : ℝ)*(base45) + (54463527/100000000000000 : ℝ)*(upper2) + (87583687/50000000000000 : ℝ)*(upper5) + (152438682988413/25000000000000 : ℝ)*(major0) + (152438682988413/25000000000000 : ℝ)*(major1) + (152438574011433/25000000000000 : ℝ)*(major2) + (127406643/25000000000000 : ℝ)*(sp1) + (403176560281609/50000000000000 : ℝ)*(sp4) + (403176053767959/50000000000000 : ℝ)*(sp5) + (40317646592777/5000000000000 : ℝ)*(sp6) + (41315582834499/10000000000000 : ℝ)*(sp7) + (41315582834499/10000000000000 : ℝ)*(f.failure) + (403176778235569/50000000000000 : ℝ)*(f.sum) + (20489378106807/12500000000000000000000000000 : ℝ)*base66 + (141640046685397/25000000000000000000000000000 : ℝ)*base68 + (47593816978217/25000000000000000000000000000 : ℝ)*base70 + (11849296235397/25000000000000000000000000000 : ℝ)*base72 + (90185350481807/12500000000000000000000000000 : ℝ)*base74 + (191754472278217/25000000000000000000000000000 : ℝ)*base76 + (37726946028217/25000000000000000000000000000 : ℝ)*base78 + (111235839028217/25000000000000000000000000000 : ℝ)*base80 + (72047519278217/12500000000000000000000000000 : ℝ)*base82 + (2441157/500000000000000000000 : ℝ)*base89 + (2441157/500000000000000000000 : ℝ)*base91 + (2441157/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1045_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28191/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1045_s1_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067265693/5000000000 : ℝ)*x 0 + (286412173/500000000 : ℝ)*x 1 + (4981310777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067265693/5000000000 : ℝ)^4119 ≤ (12805546588247/100000000000000 : ℝ)^3095 := by
    have hnat : (1067265693 : ℕ)^4119*100000000000000^3095 ≤ 12805546588247^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067265693 5000000000 12805546588247 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286412173/500000000 : ℝ)^4119 ≤ (4763886058377/10000000000000 : ℝ)^3095 := by
    have hnat : (286412173 : ℕ)^4119*10000000000000^3095 ≤ 4763886058377^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286412173 500000000 4763886058377 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981310777/10000000000 : ℝ)^4119 ≤ (39555592819541/100000000000000 : ℝ)^3095 := by
    have hnat : (4981310777 : ℕ)^4119*100000000000000^3095 ≤ 39555592819541^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981310777 10000000000 39555592819541 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067265693/5000000000 : ℝ), (286412173/500000000 : ℝ), (4981310777/10000000000 : ℝ)] ![(12805546588247/100000000000000 : ℝ), (4763886058377/10000000000000 : ℝ), (39555592819541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067265693/5000000000 : ℝ)|^4119 ≤ (12805546588247/100000000000000 : ℝ)^3095
        have hw : |(-1067265693/5000000000 : ℝ)|=(1067265693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286412173/500000000 : ℝ)|^4119 ≤ (4763886058377/10000000000000 : ℝ)^3095
        have hw : |(286412173/500000000 : ℝ)|=(286412173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981310777/10000000000 : ℝ)|^4119 ≤ (39555592819541/100000000000000 : ℝ)^3095
        have hw : |(4981310777/10000000000 : ℝ)|=(4981310777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1356117853/2500000000 : ℝ)*x 0 + (-101587089/400000000 : ℝ)*x 1 + (49813111/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356117853/2500000000 : ℝ)^4119 ≤ (44306549200111/100000000000000 : ℝ)^3095 := by
    have hnat : (1356117853 : ℕ)^4119*100000000000000^3095 ≤ 44306549200111^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356117853 2500000000 44306549200111 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101587089/400000000 : ℝ)^4119 ≤ (8068927278557/50000000000000 : ℝ)^3095 := by
    have hnat : (101587089 : ℕ)^4119*50000000000000^3095 ≤ 8068927278557^3095*400000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101587089 400000000 8068927278557 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49813111/100000000 : ℝ)^4119 ≤ (1582223849321/4000000000000 : ℝ)^3095 := by
    have hnat : (49813111 : ℕ)^4119*4000000000000^3095 ≤ 1582223849321^3095*100000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49813111 100000000 1582223849321 4000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1356117853/2500000000 : ℝ), (-101587089/400000000 : ℝ), (49813111/100000000 : ℝ)] ![(44306549200111/100000000000000 : ℝ), (8068927278557/50000000000000 : ℝ), (1582223849321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1356117853/2500000000 : ℝ)|^4119 ≤ (44306549200111/100000000000000 : ℝ)^3095
        have hw : |(1356117853/2500000000 : ℝ)|=(1356117853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101587089/400000000 : ℝ)|^4119 ≤ (8068927278557/50000000000000 : ℝ)^3095
        have hw : |(-101587089/400000000 : ℝ)|=(101587089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49813111/100000000 : ℝ)|^4119 ≤ (1582223849321/4000000000000 : ℝ)^3095
        have hw : |(49813111/100000000 : ℝ)|=(49813111/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2712235909/5000000000 : ℝ)*x 0 + (2490655299/5000000000 : ℝ)*x 1 + (-253967733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712235909/5000000000 : ℝ)^4119 ≤ (22153276806727/50000000000000 : ℝ)^3095 := by
    have hnat : (2712235909 : ℕ)^4119*50000000000000^3095 ≤ 22153276806727^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712235909 5000000000 22153276806727 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490655299/5000000000 : ℝ)^4119 ≤ (19777795463929/50000000000000 : ℝ)^3095 := by
    have hnat : (2490655299 : ℕ)^4119*50000000000000^3095 ≤ 19777795463929^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490655299 5000000000 19777795463929 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253967733/1000000000 : ℝ)^4119 ≤ (8068927722531/50000000000000 : ℝ)^3095 := by
    have hnat : (253967733 : ℕ)^4119*50000000000000^3095 ≤ 8068927722531^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253967733 1000000000 8068927722531 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712235909/5000000000 : ℝ), (2490655299/5000000000 : ℝ), (-253967733/1000000000 : ℝ)] ![(22153276806727/50000000000000 : ℝ), (19777795463929/50000000000000 : ℝ), (8068927722531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712235909/5000000000 : ℝ)|^4119 ≤ (22153276806727/50000000000000 : ℝ)^3095
        have hw : |(2712235909/5000000000 : ℝ)|=(2712235909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490655299/5000000000 : ℝ)|^4119 ≤ (19777795463929/50000000000000 : ℝ)^3095
        have hw : |(2490655299/5000000000 : ℝ)|=(2490655299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253967733/1000000000 : ℝ)|^4119 ≤ (8068927722531/50000000000000 : ℝ)^3095
        have hw : |(-253967733/1000000000 : ℝ)|=(253967733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325535771/10000000000 : ℝ)*x 0 + (3658473177/10000000000 : ℝ)*x 1 + (5116255689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325535771/10000000000 : ℝ)^4119 ≤ (32780943378701/100000000000000 : ℝ)^3095 := by
    have hnat : (4325535771 : ℕ)^4119*100000000000000^3095 ≤ 32780943378701^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325535771 10000000000 32780943378701 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3658473177/10000000000 : ℝ)^4119 ≤ (1049240182113/4000000000000 : ℝ)^3095 := by
    have hnat : (3658473177 : ℕ)^4119*4000000000000^3095 ≤ 1049240182113^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658473177 10000000000 1049240182113 4000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5116255689/10000000000 : ℝ)^4119 ≤ (20494026029087/50000000000000 : ℝ)^3095 := by
    have hnat : (5116255689 : ℕ)^4119*50000000000000^3095 ≤ 20494026029087^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116255689 10000000000 20494026029087 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325535771/10000000000 : ℝ), (3658473177/10000000000 : ℝ), (5116255689/10000000000 : ℝ)] ![(32780943378701/100000000000000 : ℝ), (1049240182113/4000000000000 : ℝ), (20494026029087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325535771/10000000000 : ℝ)|^4119 ≤ (32780943378701/100000000000000 : ℝ)^3095
        have hw : |(4325535771/10000000000 : ℝ)|=(4325535771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3658473177/10000000000 : ℝ)|^4119 ≤ (1049240182113/4000000000000 : ℝ)^3095
        have hw : |(3658473177/10000000000 : ℝ)|=(3658473177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5116255689/10000000000 : ℝ)|^4119 ≤ (20494026029087/50000000000000 : ℝ)^3095
        have hw : |(5116255689/10000000000 : ℝ)|=(5116255689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33366983/156250000 : ℝ)*x 0 + (249594533/500000000 : ℝ)*x 1 + (5717445257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33366983/156250000 : ℝ)^4119 ≤ (6406588090699/50000000000000 : ℝ)^3095 := by
    have hnat : (33366983 : ℕ)^4119*50000000000000^3095 ≤ 6406588090699^3095*156250000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33366983 156250000 6406588090699 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249594533/500000000 : ℝ)^4119 ≤ (3966744095697/10000000000000 : ℝ)^3095 := by
    have hnat : (249594533 : ℕ)^4119*10000000000000^3095 ≤ 3966744095697^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249594533 500000000 3966744095697 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5717445257/10000000000 : ℝ)^4119 ≤ (47519382839911/100000000000000 : ℝ)^3095 := by
    have hnat : (5717445257 : ℕ)^4119*100000000000000^3095 ≤ 47519382839911^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717445257 10000000000 47519382839911 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33366983/156250000 : ℝ), (249594533/500000000 : ℝ), (5717445257/10000000000 : ℝ)] ![(6406588090699/50000000000000 : ℝ), (3966744095697/10000000000000 : ℝ), (47519382839911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33366983/156250000 : ℝ)|^4119 ≤ (6406588090699/50000000000000 : ℝ)^3095
        have hw : |(-33366983/156250000 : ℝ)|=(33366983/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249594533/500000000 : ℝ)|^4119 ≤ (3966744095697/10000000000000 : ℝ)^3095
        have hw : |(249594533/500000000 : ℝ)|=(249594533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5717445257/10000000000 : ℝ)|^4119 ≤ (47519382839911/100000000000000 : ℝ)^3095
        have hw : |(5717445257/10000000000 : ℝ)|=(5717445257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261696411/500000000 : ℝ)*x 0 + (-225442679/1250000000 : ℝ)*x 1 + (1429361619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261696411/500000000 : ℝ)^4119 ≤ (8449483734723/20000000000000 : ℝ)^3095 := by
    have hnat : (261696411 : ℕ)^4119*20000000000000^3095 ≤ 8449483734723^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261696411 500000000 8449483734723 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225442679/1250000000 : ℝ)^4119 ≤ (10233184985743/100000000000000 : ℝ)^3095 := by
    have hnat : (225442679 : ℕ)^4119*100000000000000^3095 ≤ 10233184985743^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225442679 1250000000 10233184985743 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429361619/2500000000 : ℝ)^4119 ≤ (23759698161721/50000000000000 : ℝ)^3095 := by
    have hnat : (1429361619 : ℕ)^4119*50000000000000^3095 ≤ 23759698161721^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429361619 2500000000 23759698161721 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261696411/500000000 : ℝ), (-225442679/1250000000 : ℝ), (1429361619/2500000000 : ℝ)] ![(8449483734723/20000000000000 : ℝ), (10233184985743/100000000000000 : ℝ), (23759698161721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261696411/500000000 : ℝ)|^4119 ≤ (8449483734723/20000000000000 : ℝ)^3095
        have hw : |(261696411/500000000 : ℝ)|=(261696411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225442679/1250000000 : ℝ)|^4119 ≤ (10233184985743/100000000000000 : ℝ)^3095
        have hw : |(-225442679/1250000000 : ℝ)|=(225442679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1429361619/2500000000 : ℝ)|^4119 ≤ (23759698161721/50000000000000 : ℝ)^3095
        have hw : |(1429361619/2500000000 : ℝ)|=(1429361619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2616963161/5000000000 : ℝ)*x 0 + (5717448559/10000000000 : ℝ)*x 1 + (-1803541081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616963161/5000000000 : ℝ)^4119 ≤ (10561849571109/25000000000000 : ℝ)^3095 := by
    have hnat : (2616963161 : ℕ)^4119*25000000000000^3095 ≤ 10561849571109^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616963161 5000000000 10561849571109 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5717448559/10000000000 : ℝ)^4119 ≤ (47519419363801/100000000000000 : ℝ)^3095 := by
    have hnat : (5717448559 : ℕ)^4119*100000000000000^3095 ≤ 47519419363801^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717448559 10000000000 47519419363801 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1803541081/10000000000 : ℝ)^4119 ≤ (10233182335273/100000000000000 : ℝ)^3095 := by
    have hnat : (1803541081 : ℕ)^4119*100000000000000^3095 ≤ 10233182335273^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803541081 10000000000 10233182335273 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616963161/5000000000 : ℝ), (5717448559/10000000000 : ℝ), (-1803541081/10000000000 : ℝ)] ![(10561849571109/25000000000000 : ℝ), (47519419363801/100000000000000 : ℝ), (10233182335273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616963161/5000000000 : ℝ)|^4119 ≤ (10561849571109/25000000000000 : ℝ)^3095
        have hw : |(2616963161/5000000000 : ℝ)|=(2616963161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5717448559/10000000000 : ℝ)|^4119 ≤ (47519419363801/100000000000000 : ℝ)^3095
        have hw : |(5717448559/10000000000 : ℝ)|=(5717448559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1803541081/10000000000 : ℝ)|^4119 ≤ (10233182335273/100000000000000 : ℝ)^3095
        have hw : |(-1803541081/10000000000 : ℝ)|=(1803541081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s1_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865479503/2000000000 : ℝ)*x 0 + (101912073/200000000 : ℝ)*x 1 + (3679545333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865479503/2000000000 : ℝ)^4119 ≤ (32799721993767/100000000000000 : ℝ)^3095 := by
    have hnat : (865479503 : ℕ)^4119*100000000000000^3095 ≤ 32799721993767^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865479503 2000000000 32799721993767 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101912073/200000000 : ℝ)^4119 ≤ (40768008453463/100000000000000 : ℝ)^3095 := by
    have hnat : (101912073 : ℕ)^4119*100000000000000^3095 ≤ 40768008453463^3095*200000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101912073 200000000 40768008453463 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679545333/10000000000 : ℝ)^4119 ≤ (26432269546391/100000000000000 : ℝ)^3095 := by
    have hnat : (3679545333 : ℕ)^4119*100000000000000^3095 ≤ 26432269546391^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679545333 10000000000 26432269546391 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865479503/2000000000 : ℝ), (101912073/200000000 : ℝ), (3679545333/10000000000 : ℝ)] ![(32799721993767/100000000000000 : ℝ), (40768008453463/100000000000000 : ℝ), (26432269546391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865479503/2000000000 : ℝ)|^4119 ≤ (32799721993767/100000000000000 : ℝ)^3095
        have hw : |(865479503/2000000000 : ℝ)|=(865479503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101912073/200000000 : ℝ)|^4119 ≤ (40768008453463/100000000000000 : ℝ)^3095
        have hw : |(101912073/200000000 : ℝ)|=(101912073/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679545333/10000000000 : ℝ)|^4119 ≤ (26432269546391/100000000000000 : ℝ)^3095
        have hw : |(3679545333/10000000000 : ℝ)|=(3679545333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5089/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5223/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (7/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (973/50000000000000000000 : ℝ) := by
    have hpowers : (7/100000 : ℝ)^8237 ≤ (973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7 : ℕ)^8237*50000000000000000000^2048 ≤ 973^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 100000 973 50000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/100000 : ℝ)) (X := (973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28191/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (614270123579509743/100000000000000000000 : ℝ) := by
    have hpowers : (28191/100000 : ℝ)^8237 ≤ (614270123579509743/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28191 : ℕ)^8237*100000000000000000000^2048 ≤ 614270123579509743^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28191 100000 614270123579509743 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28191/100000 : ℝ)) (X := (614270123579509743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000000000973/25000000000000000000 : ℝ) ≤ (10000000000000001/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (25000000000000000973/25000000000000000000 : ℝ)^2048 ≤ (10000000000000001/10000000000000000 : ℝ)^8237 := by
      have hnat : (25000000000000000973 : ℕ)^2048*10000000000000000^8237 ≤ 10000000000000001^8237*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000000000973 25000000000000000000 10000000000000001 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000001/10000000000000000 : ℝ)) (X := (25000000000000000973/25000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100614270123579511689/100000000000000000000 : ℝ) ≤ (1001523773735049/1000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (100614270123579511689/100000000000000000000 : ℝ)^2048 ≤ (1001523773735049/1000000000000000 : ℝ)^8237 := by
      have hnat : (100614270123579511689 : ℕ)^2048*1000000000000000^8237 ≤ 1001523773735049^8237*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100614270123579511689 100000000000000000000 1001523773735049 1000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001523773735049/1000000000000000 : ℝ)) (X := (100614270123579511689/100000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50614270123579509743/50000000000000000000 : ℝ) ≤ (10030475474700979/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50614270123579509743/50000000000000000000 : ℝ)^2048 ≤ (10030475474700979/10000000000000000 : ℝ)^8237 := by
      have hnat : (50614270123579509743 : ℕ)^2048*10000000000000000^8237 ≤ 10030475474700979^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50614270123579509743 50000000000000000000 10030475474700979 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030475474700979/10000000000000000 : ℝ)) (X := (50614270123579509743/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(973/50000000000000000000 : ℝ) ≤ ((140919893335838560669/140920000000000000000 : ℝ)+2*(15237737350489/2818400000000000 : ℝ)*(7/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (140919893335838560669/140920000000000000000 : ℝ)+2*(15237737350489/2818400000000000 : ℝ)*(7/100000 : ℝ)=(10000000000000001/10000000000000000 : ℝ) by norm_num, show 1+2*(973/50000000000000000000 : ℝ)=(25000000000000000973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(614270123579509743/100000000000000000000 : ℝ)+(973/50000000000000000000 : ℝ) ≤ ((140919893335838560669/140920000000000000000 : ℝ)+(15237737350489/2818400000000000 : ℝ)*((28191/100000 : ℝ)+(7/100000 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (140919893335838560669/140920000000000000000 : ℝ)+(15237737350489/2818400000000000 : ℝ)*((28191/100000 : ℝ)+(7/100000 : ℝ))=(1001523773735049/1000000000000000 : ℝ) by norm_num, show 1+(614270123579509743/100000000000000000000 : ℝ)+(973/50000000000000000000 : ℝ)=(100614270123579511689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(614270123579509743/100000000000000000000 : ℝ) ≤ ((140919893335838560669/140920000000000000000 : ℝ)+2*(15237737350489/2818400000000000 : ℝ)*(28191/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (140919893335838560669/140920000000000000000 : ℝ)+2*(15237737350489/2818400000000000 : ℝ)*(28191/100000 : ℝ)=(10030475474700979/10000000000000000 : ℝ) by norm_num, show 1+2*(614270123579509743/100000000000000000000 : ℝ)=(50614270123579509743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (140919893335838560669/140920000000000000000 : ℝ)*(X 1 0+X 2 0)+(15237737350489/2818400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (7/100000 : ℝ)) (hi := (28191/100000 : ℝ)) (c := (140919893335838560669/140920000000000000000 : ℝ)) (alpha := (15237737350489/2818400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (140919893335838560669/140920000000000000000 : ℝ)*(X 0 1+X 2 1)+(15237737350489/2818400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (7/100000 : ℝ)) (hi := (28191/100000 : ℝ)) (c := (140919893335838560669/140920000000000000000 : ℝ)) (alpha := (15237737350489/2818400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (140919893335838560669/140920000000000000000 : ℝ)*(X 0 2+X 1 2)+(15237737350489/2818400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (7/100000 : ℝ)) (hi := (28191/100000 : ℝ)) (c := (140919893335838560669/140920000000000000000 : ℝ)) (alpha := (15237737350489/2818400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067265693/5000000000 : ℝ)*X 0 0+(286412173/500000000 : ℝ)*X 0 1+(4981310777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1356117853/2500000000 : ℝ)*X 1 0+(-101587089/400000000 : ℝ)*X 1 1+(49813111/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2712235909/5000000000 : ℝ)*X 2 0+(2490655299/5000000000 : ℝ)*X 2 1+(-253967733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325535771/10000000000 : ℝ)*X 0 0+(3658473177/10000000000 : ℝ)*X 0 1+(5116255689/10000000000 : ℝ)*X 0 2+(4325535771/10000000000 : ℝ)*X 1 0+(3658473177/10000000000 : ℝ)*X 1 1+(5116255689/10000000000 : ℝ)*X 1 2+(4325535771/10000000000 : ℝ)*X 2 0+(3658473177/10000000000 : ℝ)*X 2 1+(5116255689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33366983/156250000 : ℝ)*X 0 0+(249594533/500000000 : ℝ)*X 0 1+(5717445257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((261696411/500000000 : ℝ)*X 1 0+(-225442679/1250000000 : ℝ)*X 1 1+(1429361619/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2616963161/5000000000 : ℝ)*X 2 0+(5717448559/10000000000 : ℝ)*X 2 1+(-1803541081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865479503/2000000000 : ℝ)*X 0 0+(101912073/200000000 : ℝ)*X 0 1+(3679545333/10000000000 : ℝ)*X 0 2+(865479503/2000000000 : ℝ)*X 1 0+(101912073/200000000 : ℝ)*X 1 1+(3679545333/10000000000 : ℝ)*X 1 2+(865479503/2000000000 : ℝ)*X 2 0+(101912073/200000000 : ℝ)*X 2 1+(3679545333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4477079503966486457833952463/1409200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (892901/1250000000000 : ℝ)*(base1) + (719214847/100000000000000 : ℝ)*(base19) + (204854957/25000000000000 : ℝ)*(base23) + (40655197/50000000000000 : ℝ)*(upper3) + (73612889/100000000000000 : ℝ)*(upper5) + (202479299940791/20000000000000 : ℝ)*(major0) + (202479299940791/20000000000000 : ℝ)*(major1) + (202479299940791/20000000000000 : ℝ)*(major2) + (334703100520073/25000000000000 : ℝ)*(sp0) + (669407757142649/50000000000000 : ℝ)*(sp1) + (334703853520079/25000000000000 : ℝ)*(sp2) + (171493723898793/25000000000000 : ℝ)*(sp3) + (3902851933/100000000000000 : ℝ)*(sp4) + (846489649/50000000000000 : ℝ)*(sp7) + (13719533200131/2000000000000 : ℝ)*(f.failure) + (267763246700029/20000000000000 : ℝ)*(f.sum) + (612868126417/28184000000000000000000000000 : ℝ)*base66 + (12595321336488300821/2818400000000000000000000000000000 : ℝ)*base68 + (8287576364912499179/2818400000000000000000000000000000 : ℝ)*base69 + (1368814580214099179/2818400000000000000000000000000000 : ℝ)*base71 + (68871827936497/28184000000000000000000000000 : ℝ)*base74 + (4764910725171500821/2818400000000000000000000000000000 : ℝ)*base76 + (7237755726313299179/2818400000000000000000000000000000 : ℝ)*base77 + (10615744700340499179/2818400000000000000000000000000000 : ℝ)*base79 + (92622143483791/28184000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (603067/100000000000000000000 : ℝ)*base90 + (603067/100000000000000000000 : ℝ)*base92 + (603067/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1077236519513726733908291307/271000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50195069/2000000000000 : ℝ)*(base19) + (147344423/6250000000000 : ℝ)*(base23) + (54357/32000000000 : ℝ)*(upper2) + (363436011/100000000000000 : ℝ)*(upper3) + (505313717/100000000000000 : ℝ)*(upper5) + (521110031470429/50000000000000 : ℝ)*(major0) + (521110031470429/50000000000000 : ℝ)*(major1) + (521110031470429/50000000000000 : ℝ)*(major2) + (186656541/1562500000000 : ℝ)*(sp1) + (12577959849/100000000000000 : ℝ)*(sp2) + (17228194632503/1250000000000 : ℝ)*(sp4) + (689120557414083/50000000000000 : ℝ)*(sp5) + (1378240635129623/100000000000000 : ℝ)*(sp6) + (88273052847507/12500000000000 : ℝ)*(sp7) + (88273052847507/12500000000000 : ℝ)*(f.failure) + (17228194632503/1250000000000 : ℝ)*(f.sum) + (112824000088181/70460000000000000000000000000 : ℝ)*base65 + (49729787889685007001/7046000000000000000000000000000000 : ℝ)*base67 + (35118656027397007001/7046000000000000000000000000000000 : ℝ)*base69 + (34166444649877007001/7046000000000000000000000000000000 : ℝ)*base71 + (4407879577301/70460000000000000000000000000 : ℝ)*base73 + (29840442919541007001/7046000000000000000000000000000000 : ℝ)*base75 + (41551706167797007001/7046000000000000000000000000000000 : ℝ)*base77 + (6101064686971007001/7046000000000000000000000000000000 : ℝ)*base79 + (8530036847119/70460000000000000000000000000 : ℝ)*base82 + (738901/625000000000000000000 : ℝ)*base89 + (738901/625000000000000000000 : ℝ)*base91 + (738901/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1045_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5223/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1045_s2_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43862783/200000000 : ℝ)*x 0 + (5530303429/10000000000 : ℝ)*x 1 + (2571045553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43862783/200000000 : ℝ)^4119 ≤ (829724386659/6250000000000 : ℝ)^3095 := by
    have hnat : (43862783 : ℕ)^4119*6250000000000^3095 ≤ 829724386659^3095*200000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43862783 200000000 829724386659 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5530303429/10000000000 : ℝ)^4119 ≤ (1420646008201/3125000000000 : ℝ)^3095 := by
    have hnat : (5530303429 : ℕ)^4119*3125000000000^3095 ≤ 1420646008201^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530303429 10000000000 1420646008201 3125000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571045553/5000000000 : ℝ)^4119 ≤ (41263737533309/100000000000000 : ℝ)^3095 := by
    have hnat : (2571045553 : ℕ)^4119*100000000000000^3095 ≤ 41263737533309^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571045553 5000000000 41263737533309 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43862783/200000000 : ℝ), (5530303429/10000000000 : ℝ), (2571045553/5000000000 : ℝ)] ![(829724386659/6250000000000 : ℝ), (1420646008201/3125000000000 : ℝ), (41263737533309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43862783/200000000 : ℝ)|^4119 ≤ (829724386659/6250000000000 : ℝ)^3095
        have hw : |(-43862783/200000000 : ℝ)|=(43862783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5530303429/10000000000 : ℝ)|^4119 ≤ (1420646008201/3125000000000 : ℝ)^3095
        have hw : |(5530303429/10000000000 : ℝ)|=(5530303429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2571045553/5000000000 : ℝ)|^4119 ≤ (41263737533309/100000000000000 : ℝ)^3095
        have hw : |(2571045553/5000000000 : ℝ)|=(2571045553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075629973/2000000000 : ℝ)*x 0 + (-598945127/2500000000 : ℝ)*x 1 + (5142091667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075629973/2000000000 : ℝ)^4119 ≤ (43803732630631/100000000000000 : ℝ)^3095 := by
    have hnat : (1075629973 : ℕ)^4119*100000000000000^3095 ≤ 43803732630631^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075629973 2000000000 43803732630631 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598945127/2500000000 : ℝ)^4119 ≤ (3733130957361/25000000000000 : ℝ)^3095 := by
    have hnat : (598945127 : ℕ)^4119*25000000000000^3095 ≤ 3733130957361^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598945127 2500000000 3733130957361 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142091667/10000000000 : ℝ)^4119 ≤ (41263743524633/100000000000000 : ℝ)^3095 := by
    have hnat : (5142091667 : ℕ)^4119*100000000000000^3095 ≤ 41263743524633^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142091667 10000000000 41263743524633 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075629973/2000000000 : ℝ), (-598945127/2500000000 : ℝ), (5142091667/10000000000 : ℝ)] ![(43803732630631/100000000000000 : ℝ), (3733130957361/25000000000000 : ℝ), (41263743524633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075629973/2000000000 : ℝ)|^4119 ≤ (43803732630631/100000000000000 : ℝ)^3095
        have hw : |(1075629973/2000000000 : ℝ)|=(1075629973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-598945127/2500000000 : ℝ)|^4119 ≤ (3733130957361/25000000000000 : ℝ)^3095
        have hw : |(-598945127/2500000000 : ℝ)|=(598945127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142091667/10000000000 : ℝ)|^4119 ≤ (41263743524633/100000000000000 : ℝ)^3095
        have hw : |(5142091667/10000000000 : ℝ)|=(5142091667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378150629/10000000000 : ℝ)*x 0 + (1028417933/2000000000 : ℝ)*x 1 + (-2395782087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378150629/10000000000 : ℝ)^4119 ≤ (43803740912011/100000000000000 : ℝ)^3095 := by
    have hnat : (5378150629 : ℕ)^4119*100000000000000^3095 ≤ 43803740912011^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378150629 10000000000 43803740912011 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028417933/2000000000 : ℝ)^4119 ≤ (41263722143831/100000000000000 : ℝ)^3095 := by
    have hnat : (1028417933 : ℕ)^4119*100000000000000^3095 ≤ 41263722143831^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028417933 2000000000 41263722143831 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395782087/10000000000 : ℝ)^4119 ≤ (14932536927279/100000000000000 : ℝ)^3095 := by
    have hnat : (2395782087 : ℕ)^4119*100000000000000^3095 ≤ 14932536927279^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395782087 10000000000 14932536927279 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378150629/10000000000 : ℝ), (1028417933/2000000000 : ℝ), (-2395782087/10000000000 : ℝ)] ![(43803740912011/100000000000000 : ℝ), (41263722143831/100000000000000 : ℝ), (14932536927279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378150629/10000000000 : ℝ)|^4119 ≤ (43803740912011/100000000000000 : ℝ)^3095
        have hw : |(5378150629/10000000000 : ℝ)|=(5378150629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028417933/2000000000 : ℝ)|^4119 ≤ (41263722143831/100000000000000 : ℝ)^3095
        have hw : |(1028417933/2000000000 : ℝ)|=(1028417933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2395782087/10000000000 : ℝ)|^4119 ≤ (14932536927279/100000000000000 : ℝ)^3095
        have hw : |(-2395782087/10000000000 : ℝ)|=(2395782087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365465847/10000000000 : ℝ)*x 0 + (4003287039/10000000000 : ℝ)*x 1 + (1190241377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365465847/10000000000 : ℝ)^4119 ≤ (2074017877837/6250000000000 : ℝ)^3095 := by
    have hnat : (4365465847 : ℕ)^4119*6250000000000^3095 ≤ 2074017877837^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365465847 10000000000 2074017877837 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003287039/10000000000 : ℝ)^4119 ≤ (1478576628961/5000000000000 : ℝ)^3095 := by
    have hnat : (4003287039 : ℕ)^4119*5000000000000^3095 ≤ 1478576628961^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003287039 10000000000 1478576628961 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190241377/2500000000 : ℝ)^4119 ≤ (7448836273533/20000000000000 : ℝ)^3095 := by
    have hnat : (1190241377 : ℕ)^4119*20000000000000^3095 ≤ 7448836273533^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190241377 2500000000 7448836273533 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365465847/10000000000 : ℝ), (4003287039/10000000000 : ℝ), (1190241377/2500000000 : ℝ)] ![(2074017877837/6250000000000 : ℝ), (1478576628961/5000000000000 : ℝ), (7448836273533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365465847/10000000000 : ℝ)|^4119 ≤ (2074017877837/6250000000000 : ℝ)^3095
        have hw : |(4365465847/10000000000 : ℝ)|=(4365465847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003287039/10000000000 : ℝ)|^4119 ≤ (1478576628961/5000000000000 : ℝ)^3095
        have hw : |(4003287039/10000000000 : ℝ)|=(4003287039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190241377/2500000000 : ℝ)|^4119 ≤ (7448836273533/20000000000000 : ℝ)^3095
        have hw : |(1190241377/2500000000 : ℝ)|=(1190241377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34269899/156250000 : ℝ)*x 0 + (5144955893/10000000000 : ℝ)*x 1 + (690925917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34269899/156250000 : ℝ)^4119 ≤ (6638336404733/50000000000000 : ℝ)^3095 := by
    have hnat : (34269899 : ℕ)^4119*50000000000000^3095 ≤ 6638336404733^3095*156250000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34269899 156250000 6638336404733 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144955893/10000000000 : ℝ)^4119 ≤ (41294335480497/100000000000000 : ℝ)^3095 := by
    have hnat : (5144955893 : ℕ)^4119*100000000000000^3095 ≤ 41294335480497^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144955893 10000000000 41294335480497 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690925917/1250000000 : ℝ)^4119 ≤ (11357247924571/25000000000000 : ℝ)^3095 := by
    have hnat : (690925917 : ℕ)^4119*25000000000000^3095 ≤ 11357247924571^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690925917 1250000000 11357247924571 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34269899/156250000 : ℝ), (5144955893/10000000000 : ℝ), (690925917/1250000000 : ℝ)] ![(6638336404733/50000000000000 : ℝ), (41294335480497/100000000000000 : ℝ), (11357247924571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34269899/156250000 : ℝ)|^4119 ≤ (6638336404733/50000000000000 : ℝ)^3095
        have hw : |(-34269899/156250000 : ℝ)|=(34269899/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144955893/10000000000 : ℝ)|^4119 ≤ (41294335480497/100000000000000 : ℝ)^3095
        have hw : |(5144955893/10000000000 : ℝ)|=(5144955893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690925917/1250000000 : ℝ)|^4119 ≤ (11357247924571/25000000000000 : ℝ)^3095
        have hw : |(690925917/1250000000 : ℝ)|=(690925917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280307201/10000000000 : ℝ)*x 0 + (-1005232397/5000000000 : ℝ)*x 1 + (2763703699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280307201/10000000000 : ℝ)^4119 ≤ (42746371709399/100000000000000 : ℝ)^3095 := by
    have hnat : (5280307201 : ℕ)^4119*100000000000000^3095 ≤ 42746371709399^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280307201 10000000000 42746371709399 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005232397/5000000000 : ℝ)^4119 ≤ (5912317950587/50000000000000 : ℝ)^3095 := by
    have hnat : (1005232397 : ℕ)^4119*50000000000000^3095 ≤ 5912317950587^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005232397 5000000000 5912317950587 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2763703699/5000000000 : ℝ)^4119 ≤ (354914002941/781250000000 : ℝ)^3095 := by
    have hnat : (2763703699 : ℕ)^4119*781250000000^3095 ≤ 354914002941^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763703699 5000000000 354914002941 781250000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280307201/10000000000 : ℝ), (-1005232397/5000000000 : ℝ), (2763703699/5000000000 : ℝ)] ![(42746371709399/100000000000000 : ℝ), (5912317950587/50000000000000 : ℝ), (354914002941/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280307201/10000000000 : ℝ)|^4119 ≤ (42746371709399/100000000000000 : ℝ)^3095
        have hw : |(5280307201/10000000000 : ℝ)|=(5280307201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005232397/5000000000 : ℝ)|^4119 ≤ (5912317950587/50000000000000 : ℝ)^3095
        have hw : |(-1005232397/5000000000 : ℝ)|=(1005232397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2763703699/5000000000 : ℝ)|^4119 ≤ (354914002941/781250000000 : ℝ)^3095
        have hw : |(2763703699/5000000000 : ℝ)|=(2763703699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280307423/10000000000 : ℝ)*x 0 + (138185181/250000000 : ℝ)*x 1 + (-2010464709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280307423/10000000000 : ℝ)^4119 ≤ (8549274820239/20000000000000 : ℝ)^3095 := by
    have hnat : (5280307423 : ℕ)^4119*20000000000000^3095 ≤ 8549274820239^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280307423 10000000000 8549274820239 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138185181/250000000 : ℝ)^4119 ≤ (1817159625929/4000000000000 : ℝ)^3095 := by
    have hnat : (138185181 : ℕ)^4119*4000000000000^3095 ≤ 1817159625929^3095*250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138185181 250000000 1817159625929 4000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010464709/10000000000 : ℝ)^4119 ≤ (5912317617919/50000000000000 : ℝ)^3095 := by
    have hnat : (2010464709 : ℕ)^4119*50000000000000^3095 ≤ 5912317617919^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010464709 10000000000 5912317617919 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280307423/10000000000 : ℝ), (138185181/250000000 : ℝ), (-2010464709/10000000000 : ℝ)] ![(8549274820239/20000000000000 : ℝ), (1817159625929/4000000000000 : ℝ), (5912317617919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280307423/10000000000 : ℝ)|^4119 ≤ (8549274820239/20000000000000 : ℝ)^3095
        have hw : |(5280307423/10000000000 : ℝ)|=(5280307423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138185181/250000000 : ℝ)|^4119 ≤ (1817159625929/4000000000000 : ℝ)^3095
        have hw : |(138185181/250000000 : ℝ)|=(138185181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010464709/10000000000 : ℝ)|^4119 ≤ (5912317617919/50000000000000 : ℝ)^3095
        have hw : |(-2010464709/10000000000 : ℝ)|=(2010464709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s2_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4365728107/10000000000 : ℝ)*x 0 + (4755369353/10000000000 : ℝ)*x 1 + (4008941147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365728107/10000000000 : ℝ)^4119 ≤ (6637387848353/20000000000000 : ℝ)^3095 := by
    have hnat : (4365728107 : ℕ)^4119*20000000000000^3095 ≤ 6637387848353^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365728107 10000000000 6637387848353 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4755369353/10000000000 : ℝ)^4119 ≤ (37185930849487/100000000000000 : ℝ)^3095 := by
    have hnat : (4755369353 : ℕ)^4119*100000000000000^3095 ≤ 37185930849487^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755369353 10000000000 37185930849487 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008941147/10000000000 : ℝ)^4119 ≤ (29627129887739/100000000000000 : ℝ)^3095 := by
    have hnat : (4008941147 : ℕ)^4119*100000000000000^3095 ≤ 29627129887739^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008941147 10000000000 29627129887739 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365728107/10000000000 : ℝ), (4755369353/10000000000 : ℝ), (4008941147/10000000000 : ℝ)] ![(6637387848353/20000000000000 : ℝ), (37185930849487/100000000000000 : ℝ), (29627129887739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365728107/10000000000 : ℝ)|^4119 ≤ (6637387848353/20000000000000 : ℝ)^3095
        have hw : |(4365728107/10000000000 : ℝ)|=(4365728107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4755369353/10000000000 : ℝ)|^4119 ≤ (37185930849487/100000000000000 : ℝ)^3095
        have hw : |(4755369353/10000000000 : ℝ)|=(4755369353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008941147/10000000000 : ℝ)|^4119 ≤ (29627129887739/100000000000000 : ℝ)^3095
        have hw : |(4008941147/10000000000 : ℝ)|=(4008941147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5223/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (269/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16811/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5223/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5223/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5223/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5223/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5223/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5223/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5089/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (628219022808771/100000000000000000000 : ℝ) := by
    have hpowers : (5089/100000 : ℝ)^8237 ≤ (628219022808771/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5089 : ℕ)^8237*100000000000000000000^2048 ≤ 628219022808771^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5089 100000 628219022808771 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5089/100000 : ℝ)) (X := (628219022808771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5223/25000 : ℝ) ^ (8237/2048 : ℝ) ≤ (18406797026394759/10000000000000000000 : ℝ) := by
    have hpowers : (5223/25000 : ℝ)^8237 ≤ (18406797026394759/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5223 : ℕ)^8237*10000000000000000000^2048 ≤ 18406797026394759^2048*25000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5223 25000 18406797026394759 10000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5223/25000 : ℝ)) (X := (18406797026394759/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000628219022808771/50000000000000000000 : ℝ) ≤ (500001561960041/500000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50000628219022808771/50000000000000000000 : ℝ)^2048 ≤ (500001561960041/500000000000000 : ℝ)^8237 := by
      have hnat : (50000628219022808771 : ℕ)^2048*500000000000000^8237 ≤ 500001561960041^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000628219022808771 50000000000000000000 500001561960041 500000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001561960041/500000000000000 : ℝ)) (X := (50000628219022808771/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100184696189286756361/100000000000000000000 : ℝ) ≤ (5002294498092797/5000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (100184696189286756361/100000000000000000000 : ℝ)^2048 ≤ (5002294498092797/5000000000000000 : ℝ)^8237 := by
      have hnat : (100184696189286756361 : ℕ)^2048*5000000000000000^8237 ≤ 5002294498092797^8237*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100184696189286756361 100000000000000000000 5002294498092797 5000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002294498092797/5000000000000000 : ℝ)) (X := (100184696189286756361/100000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5018406797026394759/5000000000000000000 : ℝ) ≤ (156392918018287/156250000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (5018406797026394759/5000000000000000000 : ℝ)^2048 ≤ (156392918018287/156250000000000 : ℝ)^8237 := by
      have hnat : (5018406797026394759 : ℕ)^2048*156250000000000^8237 ≤ 156392918018287^8237*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5018406797026394759 5000000000000000000 156392918018287 156250000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156392918018287/156250000000000 : ℝ)) (X := (5018406797026394759/5000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(628219022808771/100000000000000000000 : ℝ) ≤ ((9874006551406220543/9876875000000000000 : ℝ)+2*(2278878492387/790150000000000 : ℝ)*(5089/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (9874006551406220543/9876875000000000000 : ℝ)+2*(2278878492387/790150000000000 : ℝ)*(5089/100000 : ℝ)=(500001561960041/500000000000000 : ℝ) by norm_num, show 1+2*(628219022808771/100000000000000000000 : ℝ)=(50000628219022808771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18406797026394759/10000000000000000000 : ℝ)+(628219022808771/100000000000000000000 : ℝ) ≤ ((9874006551406220543/9876875000000000000 : ℝ)+(2278878492387/790150000000000 : ℝ)*((5223/25000 : ℝ)+(5089/100000 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (9874006551406220543/9876875000000000000 : ℝ)+(2278878492387/790150000000000 : ℝ)*((5223/25000 : ℝ)+(5089/100000 : ℝ))=(5002294498092797/5000000000000000 : ℝ) by norm_num, show 1+(18406797026394759/10000000000000000000 : ℝ)+(628219022808771/100000000000000000000 : ℝ)=(100184696189286756361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18406797026394759/10000000000000000000 : ℝ) ≤ ((9874006551406220543/9876875000000000000 : ℝ)+2*(2278878492387/790150000000000 : ℝ)*(5223/25000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (9874006551406220543/9876875000000000000 : ℝ)+2*(2278878492387/790150000000000 : ℝ)*(5223/25000 : ℝ)=(156392918018287/156250000000000 : ℝ) by norm_num, show 1+2*(18406797026394759/10000000000000000000 : ℝ)=(5018406797026394759/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9874006551406220543/9876875000000000000 : ℝ)*(X 1 0+X 2 0)+(2278878492387/790150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5089/100000 : ℝ)) (hi := (5223/25000 : ℝ)) (c := (9874006551406220543/9876875000000000000 : ℝ)) (alpha := (2278878492387/790150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9874006551406220543/9876875000000000000 : ℝ)*(X 0 1+X 2 1)+(2278878492387/790150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5089/100000 : ℝ)) (hi := (5223/25000 : ℝ)) (c := (9874006551406220543/9876875000000000000 : ℝ)) (alpha := (2278878492387/790150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9874006551406220543/9876875000000000000 : ℝ)*(X 0 2+X 1 2)+(2278878492387/790150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5089/100000 : ℝ)) (hi := (5223/25000 : ℝ)) (c := (9874006551406220543/9876875000000000000 : ℝ)) (alpha := (2278878492387/790150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43862783/200000000 : ℝ)*X 0 0+(5530303429/10000000000 : ℝ)*X 0 1+(2571045553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075629973/2000000000 : ℝ)*X 1 0+(-598945127/2500000000 : ℝ)*X 1 1+(5142091667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378150629/10000000000 : ℝ)*X 2 0+(1028417933/2000000000 : ℝ)*X 2 1+(-2395782087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365465847/10000000000 : ℝ)*X 0 0+(4003287039/10000000000 : ℝ)*X 0 1+(1190241377/2500000000 : ℝ)*X 0 2+(4365465847/10000000000 : ℝ)*X 1 0+(4003287039/10000000000 : ℝ)*X 1 1+(1190241377/2500000000 : ℝ)*X 1 2+(4365465847/10000000000 : ℝ)*X 2 0+(4003287039/10000000000 : ℝ)*X 2 1+(1190241377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-34269899/156250000 : ℝ)*X 0 0+(5144955893/10000000000 : ℝ)*X 0 1+(690925917/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280307201/10000000000 : ℝ)*X 1 0+(-1005232397/5000000000 : ℝ)*X 1 1+(2763703699/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280307423/10000000000 : ℝ)*X 2 0+(138185181/250000000 : ℝ)*X 2 1+(-2010464709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365728107/10000000000 : ℝ)*X 0 0+(4755369353/10000000000 : ℝ)*X 0 1+(4008941147/10000000000 : ℝ)*X 0 2+(4365728107/10000000000 : ℝ)*X 1 0+(4755369353/10000000000 : ℝ)*X 1 1+(4008941147/10000000000 : ℝ)*X 1 2+(4365728107/10000000000 : ℝ)*X 2 0+(4755369353/10000000000 : ℝ)*X 2 1+(4008941147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1365778830833561477123892699/493843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60387411/25000000000000 : ℝ)*(base15) + (4968833/50000000000000 : ℝ)*(lower2) + (4632161/100000000000000 : ℝ)*(upper4) + (314659027/100000000000000 : ℝ)*(lower5) + (973938163152209/50000000000000 : ℝ)*(major0) + (973938163152209/50000000000000 : ℝ)*(major1) + (1947876326304419/100000000000000 : ℝ)*(major2) + (643978921994119/25000000000000 : ℝ)*(sp0) + (2575915973315047/100000000000000 : ℝ)*(sp1) + (321988625038363/12500000000000 : ℝ)*(sp2) + (659913897135889/50000000000000 : ℝ)*(sp3) + (105377643/20000000000000 : ℝ)*(sp4) + (7214557787/100000000000000 : ℝ)*(sp6) + (2137821347/25000000000000 : ℝ)*(sp7) + (659918172778583/50000000000000 : ℝ)*(f.failure) + (2575916214864691/100000000000000 : ℝ)*(f.sum) + (728602889386711/79015000000000000000000000000 : ℝ)*base66 + (1683166768903991987/493843750000000000000000000000000 : ℝ)*base67 + (9629586164362304517/987687500000000000000000000000000 : ℝ)*base69 + (2114318147705258013/493843750000000000000000000000000 : ℝ)*base72 + (366818198022469/79015000000000000000000000000 : ℝ)*base73 + (5358187710964867017/987687500000000000000000000000000 : ℝ)*base75 + (1967408496100989263/493843750000000000000000000000000 : ℝ)*base78 + (613042461097729487/493843750000000000000000000000000 : ℝ)*base79 + (16752410856097/79015000000000000000000000000 : ℝ)*base81 + (9789969/2500000000000000000000 : ℝ)*base89 + (9789969/2500000000000000000000 : ℝ)*base91 + (15210031/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392634321564652876570048251/61730468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1209129737/100000000000000 : ℝ)*(base19) + (1401679567/100000000000000 : ℝ)*(base23) + (163328763/100000000000000 : ℝ)*(upper3) + (7105523/25000000000000 : ℝ)*(lower4) + (28760041/20000000000000 : ℝ)*(upper5) + (494303119859771/25000000000000 : ℝ)*(major0) + (494303119859771/25000000000000 : ℝ)*(major1) + (494303119859771/25000000000000 : ℝ)*(major2) + (1277124463/12500000000000 : ℝ)*(sp1) + (11770811113/100000000000000 : ℝ)*(sp2) + (2614710896443959/100000000000000 : ℝ)*(sp4) + (1307349735159259/50000000000000 : ℝ)*(sp5) + (2614697723953279/100000000000000 : ℝ)*(sp6) + (167464231302349/12500000000000 : ℝ)*(sp7) + (167464231302349/12500000000000 : ℝ)*(f.failure) + (2614710896443959/100000000000000 : ℝ)*(f.sum) + (167075933241/77163085937500000000000000 : ℝ)*base66 + (22783158261681559/30865234375000000000000000000000 : ℝ)*base68 + (2755027169688061847/246921875000000000000000000000000 : ℝ)*base70 + (2368470276574343097/246921875000000000000000000000000 : ℝ)*base72 + (132043896667309/19753750000000000000000000000 : ℝ)*base73 + (1232336884702499347/246921875000000000000000000000000 : ℝ)*base76 + (565397858743843097/246921875000000000000000000000000 : ℝ)*base78 + (1200983090894804361/123460937500000000000000000000000 : ℝ)*base80 + (120189100916357/39507500000000000000000000000 : ℝ)*base82 + (886293/625000000000000000000 : ℝ)*base90 + (886293/625000000000000000000 : ℝ)*base92 + (886293/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1045_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5223/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1045_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1045_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1045_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1045_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
