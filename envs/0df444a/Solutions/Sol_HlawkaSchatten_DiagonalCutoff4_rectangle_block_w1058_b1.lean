-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:01:18.849567+00:00
-- url     : https://prove2.me/submissions/151ffa4a-2c7a-4287-bc7e-b592c6b1edaf

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
theorem support_rectangle_w1058_s3_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-275358203/1250000000 : ℝ)*x 0 + (5438475091/10000000000 : ℝ)*x 1 + (5223495583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275358203/1250000000 : ℝ)^8251 ≤ (1671002436179/12500000000000 : ℝ)^6203 := by
    have hnat : (275358203 : ℕ)^8251*12500000000000^6203 ≤ 1671002436179^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275358203 1250000000 1671002436179 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438475091/10000000000 : ℝ)^8251 ≤ (22238809504209/50000000000000 : ℝ)^6203 := by
    have hnat : (5438475091 : ℕ)^8251*50000000000000^6203 ≤ 22238809504209^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438475091 10000000000 22238809504209 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223495583/10000000000 : ℝ)^8251 ≤ (42154361493959/100000000000000 : ℝ)^6203 := by
    have hnat : (5223495583 : ℕ)^8251*100000000000000^6203 ≤ 42154361493959^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223495583 10000000000 42154361493959 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275358203/1250000000 : ℝ), (5438475091/10000000000 : ℝ), (5223495583/10000000000 : ℝ)] ![(1671002436179/12500000000000 : ℝ), (22238809504209/50000000000000 : ℝ), (42154361493959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275358203/1250000000 : ℝ)|^8251 ≤ (1671002436179/12500000000000 : ℝ)^6203
        have hw : |(-275358203/1250000000 : ℝ)|=(275358203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438475091/10000000000 : ℝ)|^8251 ≤ (22238809504209/50000000000000 : ℝ)^6203
        have hw : |(5438475091/10000000000 : ℝ)|=(5438475091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223495583/10000000000 : ℝ)|^8251 ≤ (42154361493959/100000000000000 : ℝ)^6203
        have hw : |(5223495583/10000000000 : ℝ)|=(5223495583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355897697/10000000000 : ℝ)*x 0 + (-1156487223/5000000000 : ℝ)*x 1 + (1044699143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355897697/10000000000 : ℝ)^8251 ≤ (21790779927951/50000000000000 : ℝ)^6203 := by
    have hnat : (5355897697 : ℕ)^8251*50000000000000^6203 ≤ 21790779927951^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355897697 10000000000 21790779927951 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156487223/5000000000 : ℝ)^8251 ≤ (7132038614999/50000000000000 : ℝ)^6203 := by
    have hnat : (1156487223 : ℕ)^8251*50000000000000^6203 ≤ 7132038614999^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156487223 5000000000 7132038614999 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044699143/2000000000 : ℝ)^8251 ≤ (42154362910927/100000000000000 : ℝ)^6203 := by
    have hnat : (1044699143 : ℕ)^8251*100000000000000^6203 ≤ 42154362910927^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044699143 2000000000 42154362910927 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355897697/10000000000 : ℝ), (-1156487223/5000000000 : ℝ), (1044699143/2000000000 : ℝ)] ![(21790779927951/50000000000000 : ℝ), (7132038614999/50000000000000 : ℝ), (42154362910927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355897697/10000000000 : ℝ)|^8251 ≤ (21790779927951/50000000000000 : ℝ)^6203
        have hw : |(5355897697/10000000000 : ℝ)|=(5355897697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1156487223/5000000000 : ℝ)|^8251 ≤ (7132038614999/50000000000000 : ℝ)^6203
        have hw : |(-1156487223/5000000000 : ℝ)|=(1156487223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044699143/2000000000 : ℝ)|^8251 ≤ (42154362910927/100000000000000 : ℝ)^6203
        have hw : |(1044699143/2000000000 : ℝ)|=(1044699143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355897713/10000000000 : ℝ)*x 0 + (1044699191/2000000000 : ℝ)*x 1 + (-231297411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355897713/10000000000 : ℝ)^8251 ≤ (43581560029081/100000000000000 : ℝ)^6203 := by
    have hnat : (5355897713 : ℕ)^8251*100000000000000^6203 ≤ 43581560029081^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355897713 10000000000 43581560029081 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044699191/2000000000 : ℝ)^8251 ≤ (42154365487233/100000000000000 : ℝ)^6203 := by
    have hnat : (1044699191 : ℕ)^8251*100000000000000^6203 ≤ 42154365487233^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044699191 2000000000 42154365487233 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231297411/1000000000 : ℝ)^8251 ≤ (7132037236879/50000000000000 : ℝ)^6203 := by
    have hnat : (231297411 : ℕ)^8251*50000000000000^6203 ≤ 7132037236879^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231297411 1000000000 7132037236879 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355897713/10000000000 : ℝ), (1044699191/2000000000 : ℝ), (-231297411/1000000000 : ℝ)] ![(43581560029081/100000000000000 : ℝ), (42154365487233/100000000000000 : ℝ), (7132037236879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355897713/10000000000 : ℝ)|^8251 ≤ (43581560029081/100000000000000 : ℝ)^6203
        have hw : |(5355897713/10000000000 : ℝ)|=(5355897713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044699191/2000000000 : ℝ)|^8251 ≤ (42154365487233/100000000000000 : ℝ)^6203
        have hw : |(1044699191/2000000000 : ℝ)|=(1044699191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231297411/1000000000 : ℝ)|^8251 ≤ (7132037236879/50000000000000 : ℝ)^6203
        have hw : |(-231297411/1000000000 : ℝ)|=(231297411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186888621/5000000000 : ℝ)*x 0 + (4168572177/10000000000 : ℝ)*x 1 + (4589231873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186888621/5000000000 : ℝ)^8251 ≤ (6657495427207/20000000000000 : ℝ)^6203 := by
    have hnat : (2186888621 : ℕ)^8251*20000000000000^6203 ≤ 6657495427207^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186888621 5000000000 6657495427207 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168572177/10000000000 : ℝ)^8251 ≤ (1951647074541/6250000000000 : ℝ)^6203 := by
    have hnat : (4168572177 : ℕ)^8251*6250000000000^6203 ≤ 1951647074541^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168572177 10000000000 1951647074541 6250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4589231873/10000000000 : ℝ)^8251 ≤ (35486169658293/100000000000000 : ℝ)^6203 := by
    have hnat : (4589231873 : ℕ)^8251*100000000000000^6203 ≤ 35486169658293^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4589231873 10000000000 35486169658293 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186888621/5000000000 : ℝ), (4168572177/10000000000 : ℝ), (4589231873/10000000000 : ℝ)] ![(6657495427207/20000000000000 : ℝ), (1951647074541/6250000000000 : ℝ), (35486169658293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186888621/5000000000 : ℝ)|^8251 ≤ (6657495427207/20000000000000 : ℝ)^6203
        have hw : |(2186888621/5000000000 : ℝ)|=(2186888621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168572177/10000000000 : ℝ)|^8251 ≤ (1951647074541/6250000000000 : ℝ)^6203
        have hw : |(4168572177/10000000000 : ℝ)|=(4168572177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4589231873/10000000000 : ℝ)|^8251 ≤ (35486169658293/100000000000000 : ℝ)^6203
        have hw : |(4589231873/10000000000 : ℝ)|=(4589231873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-440577743/2000000000 : ℝ)*x 0 + (52243823/100000000 : ℝ)*x 1 + (135939573/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440577743/2000000000 : ℝ)^8251 ≤ (13368205881473/100000000000000 : ℝ)^6203 := by
    have hnat : (440577743 : ℕ)^8251*100000000000000^6203 ≤ 13368205881473^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440577743 2000000000 13368205881473 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52243823/100000000 : ℝ)^8251 ≤ (421638803179/1000000000000 : ℝ)^6203 := by
    have hnat : (52243823 : ℕ)^8251*1000000000000^6203 ≤ 421638803179^6203*100000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52243823 100000000 421638803179 1000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135939573/250000000 : ℝ)^8251 ≤ (5558489223137/12500000000000 : ℝ)^6203 := by
    have hnat : (135939573 : ℕ)^8251*12500000000000^6203 ≤ 5558489223137^6203*250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135939573 250000000 5558489223137 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440577743/2000000000 : ℝ), (52243823/100000000 : ℝ), (135939573/250000000 : ℝ)] ![(13368205881473/100000000000000 : ℝ), (421638803179/1000000000000 : ℝ), (5558489223137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440577743/2000000000 : ℝ)|^8251 ≤ (13368205881473/100000000000000 : ℝ)^6203
        have hw : |(-440577743/2000000000 : ℝ)|=(440577743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52243823/100000000 : ℝ)|^8251 ≤ (421638803179/1000000000000 : ℝ)^6203
        have hw : |(52243823/100000000 : ℝ)|=(52243823/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135939573/250000000 : ℝ)|^8251 ≤ (5558489223137/12500000000000 : ℝ)^6203
        have hw : |(135939573/250000000 : ℝ)|=(135939573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301779039/10000000000 : ℝ)*x 0 + (-524721671/2500000000 : ℝ)*x 1 + (5437583279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301779039/10000000000 : ℝ)^8251 ≤ (4299677564031/10000000000000 : ℝ)^6203 := by
    have hnat : (5301779039 : ℕ)^8251*10000000000000^6203 ≤ 4299677564031^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301779039 10000000000 4299677564031 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524721671/2500000000 : ℝ)^8251 ≤ (6267653330887/50000000000000 : ℝ)^6203 := by
    have hnat : (524721671 : ℕ)^8251*50000000000000^6203 ≤ 6267653330887^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524721671 2500000000 6267653330887 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437583279/10000000000 : ℝ)^8251 ≤ (44467917690267/100000000000000 : ℝ)^6203 := by
    have hnat : (5437583279 : ℕ)^8251*100000000000000^6203 ≤ 44467917690267^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437583279 10000000000 44467917690267 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301779039/10000000000 : ℝ), (-524721671/2500000000 : ℝ), (5437583279/10000000000 : ℝ)] ![(4299677564031/10000000000000 : ℝ), (6267653330887/50000000000000 : ℝ), (44467917690267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301779039/10000000000 : ℝ)|^8251 ≤ (4299677564031/10000000000000 : ℝ)^6203
        have hw : |(5301779039/10000000000 : ℝ)|=(5301779039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524721671/2500000000 : ℝ)|^8251 ≤ (6267653330887/50000000000000 : ℝ)^6203
        have hw : |(-524721671/2500000000 : ℝ)|=(524721671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437583279/10000000000 : ℝ)|^8251 ≤ (44467917690267/100000000000000 : ℝ)^6203
        have hw : |(5437583279/10000000000 : ℝ)|=(5437583279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301778711/10000000000 : ℝ)*x 0 + (5437583247/10000000000 : ℝ)*x 1 + (-2098887171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301778711/10000000000 : ℝ)^8251 ≤ (5374596512753/12500000000000 : ℝ)^6203 := by
    have hnat : (5301778711 : ℕ)^8251*12500000000000^6203 ≤ 5374596512753^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301778711 10000000000 5374596512753 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437583247/10000000000 : ℝ)^8251 ≤ (22233958671087/50000000000000 : ℝ)^6203 := by
    have hnat : (5437583247 : ℕ)^8251*50000000000000^6203 ≤ 22233958671087^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437583247 10000000000 22233958671087 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098887171/10000000000 : ℝ)^8251 ≤ (2507062106121/20000000000000 : ℝ)^6203 := by
    have hnat : (2098887171 : ℕ)^8251*20000000000000^6203 ≤ 2507062106121^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098887171 10000000000 2507062106121 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301778711/10000000000 : ℝ), (5437583247/10000000000 : ℝ), (-2098887171/10000000000 : ℝ)] ![(5374596512753/12500000000000 : ℝ), (22233958671087/50000000000000 : ℝ), (2507062106121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301778711/10000000000 : ℝ)|^8251 ≤ (5374596512753/12500000000000 : ℝ)^6203
        have hw : |(5301778711/10000000000 : ℝ)|=(5301778711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437583247/10000000000 : ℝ)|^8251 ≤ (22233958671087/50000000000000 : ℝ)^6203
        have hw : |(5437583247/10000000000 : ℝ)|=(5437583247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098887171/10000000000 : ℝ)|^8251 ≤ (2507062106121/20000000000000 : ℝ)^6203
        have hw : |(-2098887171/10000000000 : ℝ)|=(2098887171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s3_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093455413/2500000000 : ℝ)*x 0 + (917499581/2000000000 : ℝ)*x 1 + (4170316713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093455413/2500000000 : ℝ)^8251 ≤ (4160990839963/12500000000000 : ℝ)^6203 := by
    have hnat : (1093455413 : ℕ)^8251*12500000000000^6203 ≤ 4160990839963^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093455413 2500000000 4160990839963 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917499581/2000000000 : ℝ)^8251 ≤ (1418733444147/4000000000000 : ℝ)^6203 := by
    have hnat : (917499581 : ℕ)^8251*4000000000000^6203 ≤ 1418733444147^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917499581 2000000000 1418733444147 4000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170316713/10000000000 : ℝ)^8251 ≤ (31243737151447/100000000000000 : ℝ)^6203 := by
    have hnat : (4170316713 : ℕ)^8251*100000000000000^6203 ≤ 31243737151447^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170316713 10000000000 31243737151447 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093455413/2500000000 : ℝ), (917499581/2000000000 : ℝ), (4170316713/10000000000 : ℝ)] ![(4160990839963/12500000000000 : ℝ), (1418733444147/4000000000000 : ℝ), (31243737151447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093455413/2500000000 : ℝ)|^8251 ≤ (4160990839963/12500000000000 : ℝ)^6203
        have hw : |(1093455413/2500000000 : ℝ)|=(1093455413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917499581/2000000000 : ℝ)|^8251 ≤ (1418733444147/4000000000000 : ℝ)^6203
        have hw : |(917499581/2000000000 : ℝ)|=(917499581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170316713/10000000000 : ℝ)|^8251 ≤ (31243737151447/100000000000000 : ℝ)^6203
        have hw : |(4170316713/10000000000 : ℝ)|=(4170316713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7459/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (271/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (271/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (271/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (271/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (271/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (271/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (271/3125 : ℝ) ^ (4125/1024 : ℝ) ≤ (131930221418513/2500000000000000000 : ℝ) := by
    have hpowers : (271/3125 : ℝ)^4125 ≤ (131930221418513/2500000000000000000 : ℝ)^1024 := by
      have hnat : (271 : ℕ)^4125*2500000000000000000^1024 ≤ 131930221418513^1024*3125^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        271 3125 131930221418513 2500000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (271/3125 : ℝ)) (X := (131930221418513/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16767/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (37568840824204043/50000000000000000000 : ℝ) := by
    have hpowers : (16767/100000 : ℝ)^4125 ≤ (37568840824204043/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16767 : ℕ)^4125*50000000000000000000^1024 ≤ 37568840824204043^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16767 100000 37568840824204043 50000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16767/100000 : ℝ)) (X := (37568840824204043/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250131930221418513/1250000000000000000 : ℝ) ≤ (1250032749378797/1250000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (1250131930221418513/1250000000000000000 : ℝ)^1024 ≤ (1250032749378797/1250000000000000 : ℝ)^4125 := by
      have hnat : (1250131930221418513 : ℕ)^1024*1250000000000000^4125 ≤ 1250032749378797^4125*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250131930221418513 1250000000000000000 1250032749378797 1250000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250032749378797/1250000000000000 : ℝ)) (X := (1250131930221418513/1250000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50040207445252574303/50000000000000000000 : ℝ) ≤ (5000997817815723/5000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50040207445252574303/50000000000000000000 : ℝ)^1024 ≤ (5000997817815723/5000000000000000 : ℝ)^4125 := by
      have hnat : (50040207445252574303 : ℕ)^1024*5000000000000000^4125 ≤ 5000997817815723^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040207445252574303 50000000000000000000 5000997817815723 5000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000997817815723/5000000000000000 : ℝ)) (X := (50040207445252574303/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25037568840824204043/25000000000000000000 : ℝ) ≤ (2500932319058129/2500000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (25037568840824204043/25000000000000000000 : ℝ)^1024 ≤ (2500932319058129/2500000000000000 : ℝ)^4125 := by
      have hnat : (25037568840824204043 : ℕ)^1024*2500000000000000^4125 ≤ 2500932319058129^4125*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25037568840824204043 25000000000000000000 2500932319058129 2500000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500932319058129/2500000000000000 : ℝ)) (X := (25037568840824204043/25000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(131930221418513/2500000000000000000 : ℝ) ≤ ((2023051314679648391/2023750000000000000 : ℝ)+2*(173364060107/80950000000000 : ℝ)*(271/3125 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (2023051314679648391/2023750000000000000 : ℝ)+2*(173364060107/80950000000000 : ℝ)*(271/3125 : ℝ)=(1250032749378797/1250000000000000 : ℝ) by norm_num, show 1+2*(131930221418513/2500000000000000000 : ℝ)=(1250131930221418513/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37568840824204043/50000000000000000000 : ℝ)+(131930221418513/2500000000000000000 : ℝ) ≤ ((2023051314679648391/2023750000000000000 : ℝ)+(173364060107/80950000000000 : ℝ)*((16767/100000 : ℝ)+(271/3125 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (2023051314679648391/2023750000000000000 : ℝ)+(173364060107/80950000000000 : ℝ)*((16767/100000 : ℝ)+(271/3125 : ℝ))=(5000997817815723/5000000000000000 : ℝ) by norm_num, show 1+(37568840824204043/50000000000000000000 : ℝ)+(131930221418513/2500000000000000000 : ℝ)=(50040207445252574303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37568840824204043/50000000000000000000 : ℝ) ≤ ((2023051314679648391/2023750000000000000 : ℝ)+2*(173364060107/80950000000000 : ℝ)*(16767/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (2023051314679648391/2023750000000000000 : ℝ)+2*(173364060107/80950000000000 : ℝ)*(16767/100000 : ℝ)=(2500932319058129/2500000000000000 : ℝ) by norm_num, show 1+2*(37568840824204043/50000000000000000000 : ℝ)=(25037568840824204043/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2023051314679648391/2023750000000000000 : ℝ)*(X 1 0+X 2 0)+(173364060107/80950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (271/3125 : ℝ)) (hi := (16767/100000 : ℝ)) (c := (2023051314679648391/2023750000000000000 : ℝ)) (alpha := (173364060107/80950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2023051314679648391/2023750000000000000 : ℝ)*(X 0 1+X 2 1)+(173364060107/80950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (271/3125 : ℝ)) (hi := (16767/100000 : ℝ)) (c := (2023051314679648391/2023750000000000000 : ℝ)) (alpha := (173364060107/80950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2023051314679648391/2023750000000000000 : ℝ)*(X 0 2+X 1 2)+(173364060107/80950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (271/3125 : ℝ)) (hi := (16767/100000 : ℝ)) (c := (2023051314679648391/2023750000000000000 : ℝ)) (alpha := (173364060107/80950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-275358203/1250000000 : ℝ)*X 0 0+(5438475091/10000000000 : ℝ)*X 0 1+(5223495583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355897697/10000000000 : ℝ)*X 1 0+(-1156487223/5000000000 : ℝ)*X 1 1+(1044699143/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355897713/10000000000 : ℝ)*X 2 0+(1044699191/2000000000 : ℝ)*X 2 1+(-231297411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186888621/5000000000 : ℝ)*X 0 0+(4168572177/10000000000 : ℝ)*X 0 1+(4589231873/10000000000 : ℝ)*X 0 2+(2186888621/5000000000 : ℝ)*X 1 0+(4168572177/10000000000 : ℝ)*X 1 1+(4589231873/10000000000 : ℝ)*X 1 2+(2186888621/5000000000 : ℝ)*X 2 0+(4168572177/10000000000 : ℝ)*X 2 1+(4589231873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-440577743/2000000000 : ℝ)*X 0 0+(52243823/100000000 : ℝ)*X 0 1+(135939573/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301779039/10000000000 : ℝ)*X 1 0+(-524721671/2500000000 : ℝ)*X 1 1+(5437583279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301778711/10000000000 : ℝ)*X 2 0+(5437583247/10000000000 : ℝ)*X 2 1+(-2098887171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093455413/2500000000 : ℝ)*X 0 0+(917499581/2000000000 : ℝ)*X 0 1+(4170316713/10000000000 : ℝ)*X 0 2+(1093455413/2500000000 : ℝ)*X 1 0+(917499581/2000000000 : ℝ)*X 1 1+(4170316713/10000000000 : ℝ)*X 1 2+(1093455413/2500000000 : ℝ)*X 2 0+(917499581/2000000000 : ℝ)*X 2 1+(4170316713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75607369314333858940867821/10118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940202039/50000000000000 : ℝ)*(base19) + (784260063/50000000000000 : ℝ)*(base23) + (174484537/100000000000000 : ℝ)*(lower2) + (116349249/100000000000000 : ℝ)*(upper3) + (23848631/12500000000000 : ℝ)*(upper5) + (351446451241359/10000000000000 : ℝ)*(major0) + (351446451241359/10000000000000 : ℝ)*(major1) + (351446451241359/10000000000000 : ℝ)*(major2) + (581455000615531/12500000000000 : ℝ)*(sp0) + (2325838755828707/50000000000000 : ℝ)*(sp1) + (930335564708273/20000000000000 : ℝ)*(sp2) + (1188616873987287/50000000000000 : ℝ)*(sp3) + (9846784311/25000000000000 : ℝ)*(sp4) + (15635724211/100000000000000 : ℝ)*(sp7) + (74289043240587/3125000000000 : ℝ)*(f.failure) + (1162919848015373/25000000000000 : ℝ)*(f.sum) + (19448091419/40475000000000000000000000 : ℝ)*base65 + (48154873851409131/20237500000000000000000000000000 : ℝ)*base68 + (399279774792309131/20237500000000000000000000000000 : ℝ)*base70 + (8111817324196631/20237500000000000000000000000000 : ℝ)*base72 + (3707579211981/1619000000000000000000000000 : ℝ)*base73 + (424153927799484131/20237500000000000000000000000000 : ℝ)*base76 + (211879616452359131/20237500000000000000000000000000 : ℝ)*base78 + (18575557808071631/20237500000000000000000000000000 : ℝ)*base80 + (13641159302853/1619000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (244869/62500000000000000000 : ℝ)*base89 + (244869/62500000000000000000 : ℝ)*base91 + (244869/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83544755284076579045427/8095000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2464202191/100000000000000 : ℝ)*(base19) + (533012627/25000000000000 : ℝ)*(base23) + (22455849/6250000000000 : ℝ)*(upper3) + (1105991/10000000000000 : ℝ)*(lower4) + (7283133/6250000000000 : ℝ)*(upper5) + (1771862572112847/50000000000000 : ℝ)*(major0) + (1771862572112847/50000000000000 : ℝ)*(major1) + (1771862572112847/50000000000000 : ℝ)*(major2) + (21798645827/50000000000000 : ℝ)*(sp1) + (7488261299/20000000000000 : ℝ)*(sp2) + (2345204061655169/50000000000000 : ℝ)*(sp4) + (1172590515454123/25000000000000 : ℝ)*(sp5) + (938073709990667/20000000000000 : ℝ)*(sp6) + (239704182112311/10000000000000 : ℝ)*(sp7) + (239704182112311/10000000000000 : ℝ)*(f.failure) + (2345204061655169/50000000000000 : ℝ)*(f.sum) + (25769425841883/4047500000000000000000000000 : ℝ)*base65 + (472607969734079177/101187500000000000000000000000000 : ℝ)*base67 + (674115810913420823/101187500000000000000000000000000 : ℝ)*base70 + (264857437873670823/101187500000000000000000000000000 : ℝ)*base72 + (9587212066203/4047500000000000000000000000 : ℝ)*base73 + (967988035696454177/101187500000000000000000000000000 : ℝ)*base75 + (220542531677204177/101187500000000000000000000000000 : ℝ)*base77 + (1178902468036545823/101187500000000000000000000000000 : ℝ)*base80 + (26343027112509/8095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32457/200000000000000000000 : ℝ)*base89 + (32457/200000000000000000000 : ℝ)*base91 + (32457/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1058_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7459/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1058_s4_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2206619317/10000000000 : ℝ)*x 0 + (2703134083/5000000000 : ℝ)*x 1 + (525325091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206619317/10000000000 : ℝ)^8251 ≤ (6699164004511/50000000000000 : ℝ)^6203 := by
    have hnat : (2206619317 : ℕ)^8251*50000000000000^6203 ≤ 6699164004511^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206619317 10000000000 6699164004511 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703134083/5000000000 : ℝ)^8251 ≤ (8825519761729/20000000000000 : ℝ)^6203 := by
    have hnat : (2703134083 : ℕ)^8251*20000000000000^6203 ≤ 8825519761729^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703134083 5000000000 8825519761729 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525325091/1000000000 : ℝ)^8251 ≤ (21237036588821/50000000000000 : ℝ)^6203 := by
    have hnat : (525325091 : ℕ)^8251*50000000000000^6203 ≤ 21237036588821^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525325091 1000000000 21237036588821 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2206619317/10000000000 : ℝ), (2703134083/5000000000 : ℝ), (525325091/1000000000 : ℝ)] ![(6699164004511/50000000000000 : ℝ), (8825519761729/20000000000000 : ℝ), (21237036588821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2206619317/10000000000 : ℝ)|^8251 ≤ (6699164004511/50000000000000 : ℝ)^6203
        have hw : |(-2206619317/10000000000 : ℝ)|=(2206619317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703134083/5000000000 : ℝ)|^8251 ≤ (8825519761729/20000000000000 : ℝ)^6203
        have hw : |(2703134083/5000000000 : ℝ)|=(2703134083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525325091/1000000000 : ℝ)|^8251 ≤ (21237036588821/50000000000000 : ℝ)^6203
        have hw : |(525325091/1000000000 : ℝ)|=(525325091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347927223/10000000000 : ℝ)*x 0 + (-1142227637/5000000000 : ℝ)*x 1 + (5253251503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347927223/10000000000 : ℝ)^8251 ≤ (347962489003/800000000000 : ℝ)^6203 := by
    have hnat : (5347927223 : ℕ)^8251*800000000000^6203 ≤ 347962489003^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347927223 10000000000 347962489003 800000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142227637/5000000000 : ℝ)^8251 ≤ (7015304653243/50000000000000 : ℝ)^6203 := by
    have hnat : (1142227637 : ℕ)^8251*50000000000000^6203 ≤ 7015304653243^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142227637 5000000000 7015304653243 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253251503/10000000000 : ℝ)^8251 ≤ (10618519888803/25000000000000 : ℝ)^6203 := by
    have hnat : (5253251503 : ℕ)^8251*25000000000000^6203 ≤ 10618519888803^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253251503 10000000000 10618519888803 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347927223/10000000000 : ℝ), (-1142227637/5000000000 : ℝ), (5253251503/10000000000 : ℝ)] ![(347962489003/800000000000 : ℝ), (7015304653243/50000000000000 : ℝ), (10618519888803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347927223/10000000000 : ℝ)|^8251 ≤ (347962489003/800000000000 : ℝ)^6203
        have hw : |(5347927223/10000000000 : ℝ)|=(5347927223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142227637/5000000000 : ℝ)|^8251 ≤ (7015304653243/50000000000000 : ℝ)^6203
        have hw : |(-1142227637/5000000000 : ℝ)|=(1142227637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253251503/10000000000 : ℝ)|^8251 ≤ (10618519888803/25000000000000 : ℝ)^6203
        have hw : |(5253251503/10000000000 : ℝ)|=(5253251503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347926719/10000000000 : ℝ)*x 0 + (5253251969/10000000000 : ℝ)*x 1 + (-2284455329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347926719/10000000000 : ℝ)^8251 ≤ (43495305672917/100000000000000 : ℝ)^6203 := by
    have hnat : (5347926719 : ℕ)^8251*100000000000000^6203 ≤ 43495305672917^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347926719 10000000000 43495305672917 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253251969/10000000000 : ℝ)^8251 ≤ (42474084566929/100000000000000 : ℝ)^6203 := by
    have hnat : (5253251969 : ℕ)^8251*100000000000000^6203 ≤ 42474084566929^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253251969 10000000000 42474084566929 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284455329/10000000000 : ℝ)^8251 ≤ (3507652438953/25000000000000 : ℝ)^6203 := by
    have hnat : (2284455329 : ℕ)^8251*25000000000000^6203 ≤ 3507652438953^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284455329 10000000000 3507652438953 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347926719/10000000000 : ℝ), (5253251969/10000000000 : ℝ), (-2284455329/10000000000 : ℝ)] ![(43495305672917/100000000000000 : ℝ), (42474084566929/100000000000000 : ℝ), (3507652438953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347926719/10000000000 : ℝ)|^8251 ≤ (43495305672917/100000000000000 : ℝ)^6203
        have hw : |(5347926719/10000000000 : ℝ)|=(5347926719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253251969/10000000000 : ℝ)|^8251 ≤ (42474084566929/100000000000000 : ℝ)^6203
        have hw : |(5253251969/10000000000 : ℝ)|=(5253251969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284455329/10000000000 : ℝ)|^8251 ≤ (3507652438953/25000000000000 : ℝ)^6203
        have hw : |(-2284455329/10000000000 : ℝ)|=(2284455329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34187583/78125000 : ℝ)*x 0 + (2114450731/5000000000 : ℝ)*x 1 + (4528316009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34187583/78125000 : ℝ)^8251 ≤ (33310088597927/100000000000000 : ℝ)^6203 := by
    have hnat : (34187583 : ℕ)^8251*100000000000000^6203 ≤ 33310088597927^6203*78125000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34187583 78125000 33310088597927 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114450731/5000000000 : ℝ)^8251 ≤ (31828912706799/100000000000000 : ℝ)^6203 := by
    have hnat : (2114450731 : ℕ)^8251*100000000000000^6203 ≤ 31828912706799^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114450731 5000000000 31828912706799 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528316009/10000000000 : ℝ)^8251 ≤ (4357624834681/12500000000000 : ℝ)^6203 := by
    have hnat : (4528316009 : ℕ)^8251*12500000000000^6203 ≤ 4357624834681^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528316009 10000000000 4357624834681 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34187583/78125000 : ℝ), (2114450731/5000000000 : ℝ), (4528316009/10000000000 : ℝ)] ![(33310088597927/100000000000000 : ℝ), (31828912706799/100000000000000 : ℝ), (4357624834681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34187583/78125000 : ℝ)|^8251 ≤ (33310088597927/100000000000000 : ℝ)^6203
        have hw : |(34187583/78125000 : ℝ)|=(34187583/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114450731/5000000000 : ℝ)|^8251 ≤ (31828912706799/100000000000000 : ℝ)^6203
        have hw : |(2114450731/5000000000 : ℝ)|=(2114450731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528316009/10000000000 : ℝ)|^8251 ≤ (4357624834681/12500000000000 : ℝ)^6203
        have hw : |(4528316009/10000000000 : ℝ)|=(4528316009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-275828399/1250000000 : ℝ)*x 0 + (42029613/80000000 : ℝ)*x 1 + (675726979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275828399/1250000000 : ℝ)^8251 ≤ (66991958061/500000000000 : ℝ)^6203 := by
    have hnat : (275828399 : ℕ)^8251*500000000000^6203 ≤ 66991958061^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275828399 1250000000 66991958061 500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42029613/80000000 : ℝ)^8251 ≤ (21239460288133/50000000000000 : ℝ)^6203 := by
    have hnat : (42029613 : ℕ)^8251*50000000000000^6203 ≤ 21239460288133^6203*80000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42029613 80000000 21239460288133 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675726979/1250000000 : ℝ)^8251 ≤ (22061343899697/50000000000000 : ℝ)^6203 := by
    have hnat : (675726979 : ℕ)^8251*50000000000000^6203 ≤ 22061343899697^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675726979 1250000000 22061343899697 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275828399/1250000000 : ℝ), (42029613/80000000 : ℝ), (675726979/1250000000 : ℝ)] ![(66991958061/500000000000 : ℝ), (21239460288133/50000000000000 : ℝ), (22061343899697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275828399/1250000000 : ℝ)|^8251 ≤ (66991958061/500000000000 : ℝ)^6203
        have hw : |(-275828399/1250000000 : ℝ)|=(275828399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42029613/80000000 : ℝ)|^8251 ≤ (21239460288133/50000000000000 : ℝ)^6203
        have hw : |(42029613/80000000 : ℝ)|=(42029613/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675726979/1250000000 : ℝ)|^8251 ≤ (22061343899697/50000000000000 : ℝ)^6203
        have hw : |(675726979/1250000000 : ℝ)|=(675726979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309412533/10000000000 : ℝ)*x 0 + (-1065944919/5000000000 : ℝ)*x 1 + (5405816027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309412533/10000000000 : ℝ)^8251 ≤ (43079141193363/100000000000000 : ℝ)^6203 := by
    have hnat : (5309412533 : ℕ)^8251*100000000000000^6203 ≤ 43079141193363^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309412533 10000000000 43079141193363 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065944919/5000000000 : ℝ)^8251 ≤ (1599771109697/12500000000000 : ℝ)^6203 := by
    have hnat : (1065944919 : ℕ)^8251*12500000000000^6203 ≤ 1599771109697^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065944919 5000000000 1599771109697 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405816027/10000000000 : ℝ)^8251 ≤ (5515336239561/12500000000000 : ℝ)^6203 := by
    have hnat : (5405816027 : ℕ)^8251*12500000000000^6203 ≤ 5515336239561^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405816027 10000000000 5515336239561 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309412533/10000000000 : ℝ), (-1065944919/5000000000 : ℝ), (5405816027/10000000000 : ℝ)] ![(43079141193363/100000000000000 : ℝ), (1599771109697/12500000000000 : ℝ), (5515336239561/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309412533/10000000000 : ℝ)|^8251 ≤ (43079141193363/100000000000000 : ℝ)^6203
        have hw : |(5309412533/10000000000 : ℝ)|=(5309412533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065944919/5000000000 : ℝ)|^8251 ≤ (1599771109697/12500000000000 : ℝ)^6203
        have hw : |(-1065944919/5000000000 : ℝ)|=(1065944919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405816027/10000000000 : ℝ)|^8251 ≤ (5515336239561/12500000000000 : ℝ)^6203
        have hw : |(5405816027/10000000000 : ℝ)|=(5405816027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327352963/2500000000 : ℝ)*x 0 + (2702908093/5000000000 : ℝ)*x 1 + (-2131890543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327352963/2500000000 : ℝ)^8251 ≤ (8615826768723/20000000000000 : ℝ)^6203 := by
    have hnat : (1327352963 : ℕ)^8251*20000000000000^6203 ≤ 8615826768723^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327352963 2500000000 8615826768723 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702908093/5000000000 : ℝ)^8251 ≤ (22061345821367/50000000000000 : ℝ)^6203 := by
    have hnat : (2702908093 : ℕ)^8251*50000000000000^6203 ≤ 22061345821367^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702908093 5000000000 22061345821367 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131890543/10000000000 : ℝ)^8251 ≤ (1279817450717/10000000000000 : ℝ)^6203 := by
    have hnat : (2131890543 : ℕ)^8251*10000000000000^6203 ≤ 1279817450717^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131890543 10000000000 1279817450717 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327352963/2500000000 : ℝ), (2702908093/5000000000 : ℝ), (-2131890543/10000000000 : ℝ)] ![(8615826768723/20000000000000 : ℝ), (22061345821367/50000000000000 : ℝ), (1279817450717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327352963/2500000000 : ℝ)|^8251 ≤ (8615826768723/20000000000000 : ℝ)^6203
        have hw : |(1327352963/2500000000 : ℝ)|=(1327352963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702908093/5000000000 : ℝ)|^8251 ≤ (22061345821367/50000000000000 : ℝ)^6203
        have hw : |(2702908093/5000000000 : ℝ)|=(2702908093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131890543/10000000000 : ℝ)|^8251 ≤ (1279817450717/10000000000000 : ℝ)^6203
        have hw : |(-2131890543/10000000000 : ℝ)|=(2131890543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s4_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376026637/10000000000 : ℝ)*x 0 + (2263717577/5000000000 : ℝ)*x 1 + (4229786183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376026637/10000000000 : ℝ)^8251 ≤ (2081890670771/6250000000000 : ℝ)^6203 := by
    have hnat : (4376026637 : ℕ)^8251*6250000000000^6203 ≤ 2081890670771^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376026637 10000000000 2081890670771 6250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263717577/5000000000 : ℝ)^8251 ≤ (4356497355857/12500000000000 : ℝ)^6203 := by
    have hnat : (2263717577 : ℕ)^8251*12500000000000^6203 ≤ 4356497355857^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263717577 5000000000 4356497355857 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229786183/10000000000 : ℝ)^8251 ≤ (1989860649673/6250000000000 : ℝ)^6203 := by
    have hnat : (4229786183 : ℕ)^8251*6250000000000^6203 ≤ 1989860649673^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229786183 10000000000 1989860649673 6250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376026637/10000000000 : ℝ), (2263717577/5000000000 : ℝ), (4229786183/10000000000 : ℝ)] ![(2081890670771/6250000000000 : ℝ), (4356497355857/12500000000000 : ℝ), (1989860649673/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376026637/10000000000 : ℝ)|^8251 ≤ (2081890670771/6250000000000 : ℝ)^6203
        have hw : |(4376026637/10000000000 : ℝ)|=(4376026637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263717577/5000000000 : ℝ)|^8251 ≤ (4356497355857/12500000000000 : ℝ)^6203
        have hw : |(2263717577/5000000000 : ℝ)|=(2263717577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229786183/10000000000 : ℝ)|^8251 ≤ (1989860649673/6250000000000 : ℝ)^6203
        have hw : |(4229786183/10000000000 : ℝ)|=(4229786183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7459/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2849/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7459/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7459/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7459/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7459/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7459/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7459/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10369/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (21682175445499/200000000000000000 : ℝ) := by
    have hpowers : (10369/100000 : ℝ)^4125 ≤ (21682175445499/200000000000000000 : ℝ)^1024 := by
      have hnat : (10369 : ℕ)^4125*200000000000000000^1024 ≤ 21682175445499^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10369 100000 21682175445499 200000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10369/100000 : ℝ)) (X := (21682175445499/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7459/50000 : ℝ) ^ (4125/1024 : ℝ) ≤ (46929036447644537/100000000000000000000 : ℝ) := by
    have hpowers : (7459/50000 : ℝ)^4125 ≤ (46929036447644537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7459 : ℕ)^4125*100000000000000000000^1024 ≤ 46929036447644537^1024*50000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7459 50000 46929036447644537 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7459/50000 : ℝ)) (X := (46929036447644537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (100021682175445499/100000000000000000 : ℝ) ≤ (5000269099859473/5000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (100021682175445499/100000000000000000 : ℝ)^1024 ≤ (5000269099859473/5000000000000000 : ℝ)^4125 := by
      have hnat : (100021682175445499 : ℕ)^1024*5000000000000000^4125 ≤ 5000269099859473^4125*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021682175445499 100000000000000000 5000269099859473 5000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269099859473/5000000000000000 : ℝ)) (X := (100021682175445499/100000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057770124170394037/100000000000000000000 : ℝ) ≤ (10001433788263819/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (100057770124170394037/100000000000000000000 : ℝ)^1024 ≤ (10001433788263819/10000000000000000 : ℝ)^4125 := by
      have hnat : (100057770124170394037 : ℕ)^1024*10000000000000000^4125 ≤ 10001433788263819^4125*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057770124170394037 100000000000000000000 10001433788263819 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001433788263819/10000000000000000 : ℝ)) (X := (100057770124170394037/100000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046929036447644537/50000000000000000000 : ℝ) ≤ (2500582344202173/2500000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50046929036447644537/50000000000000000000 : ℝ)^1024 ≤ (2500582344202173/2500000000000000 : ℝ)^4125 := by
      have hnat : (50046929036447644537 : ℕ)^1024*2500000000000000^4125 ≤ 2500582344202173^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046929036447644537 50000000000000000000 2500582344202173 2500000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500582344202173/2500000000000000 : ℝ)) (X := (50046929036447644537/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21682175445499/200000000000000000 : ℝ) ≤ ((1136846888881947727/1137250000000000000 : ℝ)+2*(895588544873/454900000000000 : ℝ)*(10369/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (1136846888881947727/1137250000000000000 : ℝ)+2*(895588544873/454900000000000 : ℝ)*(10369/100000 : ℝ)=(5000269099859473/5000000000000000 : ℝ) by norm_num, show 1+2*(21682175445499/200000000000000000 : ℝ)=(100021682175445499/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46929036447644537/100000000000000000000 : ℝ)+(21682175445499/200000000000000000 : ℝ) ≤ ((1136846888881947727/1137250000000000000 : ℝ)+(895588544873/454900000000000 : ℝ)*((7459/50000 : ℝ)+(10369/100000 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (1136846888881947727/1137250000000000000 : ℝ)+(895588544873/454900000000000 : ℝ)*((7459/50000 : ℝ)+(10369/100000 : ℝ))=(10001433788263819/10000000000000000 : ℝ) by norm_num, show 1+(46929036447644537/100000000000000000000 : ℝ)+(21682175445499/200000000000000000 : ℝ)=(100057770124170394037/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46929036447644537/100000000000000000000 : ℝ) ≤ ((1136846888881947727/1137250000000000000 : ℝ)+2*(895588544873/454900000000000 : ℝ)*(7459/50000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (1136846888881947727/1137250000000000000 : ℝ)+2*(895588544873/454900000000000 : ℝ)*(7459/50000 : ℝ)=(2500582344202173/2500000000000000 : ℝ) by norm_num, show 1+2*(46929036447644537/100000000000000000000 : ℝ)=(50046929036447644537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1136846888881947727/1137250000000000000 : ℝ)*(X 1 0+X 2 0)+(895588544873/454900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (10369/100000 : ℝ)) (hi := (7459/50000 : ℝ)) (c := (1136846888881947727/1137250000000000000 : ℝ)) (alpha := (895588544873/454900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1136846888881947727/1137250000000000000 : ℝ)*(X 0 1+X 2 1)+(895588544873/454900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (10369/100000 : ℝ)) (hi := (7459/50000 : ℝ)) (c := (1136846888881947727/1137250000000000000 : ℝ)) (alpha := (895588544873/454900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1136846888881947727/1137250000000000000 : ℝ)*(X 0 2+X 1 2)+(895588544873/454900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (10369/100000 : ℝ)) (hi := (7459/50000 : ℝ)) (c := (1136846888881947727/1137250000000000000 : ℝ)) (alpha := (895588544873/454900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2206619317/10000000000 : ℝ)*X 0 0+(2703134083/5000000000 : ℝ)*X 0 1+(525325091/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347927223/10000000000 : ℝ)*X 1 0+(-1142227637/5000000000 : ℝ)*X 1 1+(5253251503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347926719/10000000000 : ℝ)*X 2 0+(5253251969/10000000000 : ℝ)*X 2 1+(-2284455329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34187583/78125000 : ℝ)*X 0 0+(2114450731/5000000000 : ℝ)*X 0 1+(4528316009/10000000000 : ℝ)*X 0 2+(34187583/78125000 : ℝ)*X 1 0+(2114450731/5000000000 : ℝ)*X 1 1+(4528316009/10000000000 : ℝ)*X 1 2+(34187583/78125000 : ℝ)*X 2 0+(2114450731/5000000000 : ℝ)*X 2 1+(4528316009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-275828399/1250000000 : ℝ)*X 0 0+(42029613/80000000 : ℝ)*X 0 1+(675726979/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309412533/10000000000 : ℝ)*X 1 0+(-1065944919/5000000000 : ℝ)*X 1 1+(5405816027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327352963/2500000000 : ℝ)*X 2 0+(2702908093/5000000000 : ℝ)*X 2 1+(-2131890543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376026637/10000000000 : ℝ)*X 0 0+(2263717577/5000000000 : ℝ)*X 0 1+(4229786183/10000000000 : ℝ)*X 0 2+(4376026637/10000000000 : ℝ)*X 1 0+(2263717577/5000000000 : ℝ)*X 1 1+(4229786183/10000000000 : ℝ)*X 1 2+(4376026637/10000000000 : ℝ)*X 2 0+(2263717577/5000000000 : ℝ)*X 2 1+(4229786183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60284520679547806857304563/11372500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183915333/100000000000000 : ℝ)*(base19) + (23112467/20000000000000 : ℝ)*(upper2) + (40788509/50000000000000 : ℝ)*(upper3) + (5772929/5000000000000 : ℝ)*(lower4) + (105475163/50000000000000 : ℝ)*(upper5) + (987512860315577/20000000000000 : ℝ)*(major0) + (987512860315577/20000000000000 : ℝ)*(major1) + (987512860315577/20000000000000 : ℝ)*(major2) + (1633810502599987/25000000000000 : ℝ)*(sp0) + (3267633801668447/50000000000000 : ℝ)*(sp1) + (3267633893626113/50000000000000 : ℝ)*(sp2) + (1669929660534423/50000000000000 : ℝ)*(sp3) + (12888426139/50000000000000 : ℝ)*(sp4) + (1318137919/100000000000000 : ℝ)*(sp7) + (667972127841353/20000000000000 : ℝ)*(f.failure) + (3267633893626113/50000000000000 : ℝ)*(f.sum) + (43433448911057/2274500000000000000000000000 : ℝ)*base66 + (5721922143125979/22745000000000000000000000000000 : ℝ)*base67 + (172813918889230979/22745000000000000000000000000000 : ℝ)*base69 + (156139894696759021/22745000000000000000000000000000 : ℝ)*base72 + (14516640454957/4549000000000000000000000000 : ℝ)*base74 + (254963543246260979/22745000000000000000000000000000 : ℝ)*base75 + (64130936644099021/22745000000000000000000000000000 : ℝ)*base78 + (250910159093505979/22745000000000000000000000000000 : ℝ)*base79 + (3178562460649/568625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2889911/400000000000000000000 : ℝ)*base89 + (2889911/400000000000000000000 : ℝ)*base91 + (2889911/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16525793190842085250958787/1776953125000000000000000000000 : ℝ) := by norm_num
    linear_combination (2386673023/100000000000000 : ℝ)*(base19) + (221113767/12500000000000 : ℝ)*(base23) + (10904349/50000000000000 : ℝ)*(upper3) + (231888617/100000000000000 : ℝ)*(lower4) + (64014719/50000000000000 : ℝ)*(upper5) + (620853209383083/12500000000000 : ℝ)*(major0) + (620853209383083/12500000000000 : ℝ)*(major1) + (620853209383083/12500000000000 : ℝ)*(major2) + (4927692701/6250000000000 : ℝ)*(sp1) + (49712330343/100000000000000 : ℝ)*(sp2) + (3286998730906609/50000000000000 : ℝ)*(sp4) + (6573916232056979/100000000000000 : ℝ)*(sp5) + (6573945980572739/100000000000000 : ℝ)*(sp6) + (1679826789156841/50000000000000 : ℝ)*(sp7) + (1679826789156841/50000000000000 : ℝ)*(f.failure) + (3286998730906609/50000000000000 : ℝ)*(f.sum) + (36851638943031/11372500000000000000000000000 : ℝ)*base65 + (39328052430806091/14215625000000000000000000000000 : ℝ)*base67 + (9319338536131091/14215625000000000000000000000000 : ℝ)*base69 + (639228042971731/222119140625000000000000000000 : ℝ)*base72 + (15959300347191/11372500000000000000000000000 : ℝ)*base73 + (98902642292942267/7107812500000000000000000000000 : ℝ)*base76 + (24047090184829767/7107812500000000000000000000000 : ℝ)*base78 + (9204734980590049/888476562500000000000000000000 : ℝ)*base80 + (53915434922209/11372500000000000000000000000 : ℝ)*base82 + (2771433/1000000000000000000000 : ℝ)*base90 + (2771433/1000000000000000000000 : ℝ)*base92 + (2771433/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7459/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1058_s5_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207470559/10000000000 : ℝ)*x 0 + (674654071/1250000000 : ℝ)*x 1 + (657716061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207470559/10000000000 : ℝ)^8251 ≤ (13405203578789/100000000000000 : ℝ)^6203 := by
    have hnat : (2207470559 : ℕ)^8251*100000000000000^6203 ≤ 13405203578789^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207470559 10000000000 13405203578789 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674654071/1250000000 : ℝ)^8251 ≤ (8805904932589/20000000000000 : ℝ)^6203 := by
    have hnat : (674654071 : ℕ)^8251*20000000000000^6203 ≤ 8805904932589^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674654071 1250000000 8805904932589 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657716061/1250000000 : ℝ)^8251 ≤ (4256527174327/10000000000000 : ℝ)^6203 := by
    have hnat : (657716061 : ℕ)^8251*10000000000000^6203 ≤ 4256527174327^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657716061 1250000000 4256527174327 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207470559/10000000000 : ℝ), (674654071/1250000000 : ℝ), (657716061/1250000000 : ℝ)] ![(13405203578789/100000000000000 : ℝ), (8805904932589/20000000000000 : ℝ), (4256527174327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207470559/10000000000 : ℝ)|^8251 ≤ (13405203578789/100000000000000 : ℝ)^6203
        have hw : |(-2207470559/10000000000 : ℝ)|=(2207470559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674654071/1250000000 : ℝ)|^8251 ≤ (8805904932589/20000000000000 : ℝ)^6203
        have hw : |(674654071/1250000000 : ℝ)|=(674654071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657716061/1250000000 : ℝ)|^8251 ≤ (4256527174327/10000000000000 : ℝ)^6203
        have hw : |(657716061/1250000000 : ℝ)|=(657716061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345679713/10000000000 : ℝ)*x 0 + (-2276264211/10000000000 : ℝ)*x 1 + (2630864163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345679713/10000000000 : ℝ)^8251 ≤ (43470998421637/100000000000000 : ℝ)^6203 := by
    have hnat : (5345679713 : ℕ)^8251*100000000000000^6203 ≤ 43470998421637^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345679713 10000000000 43470998421637 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276264211/10000000000 : ℝ)^8251 ≤ (6981865782487/50000000000000 : ℝ)^6203 := by
    have hnat : (2276264211 : ℕ)^8251*50000000000000^6203 ≤ 6981865782487^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276264211 10000000000 6981865782487 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630864163/5000000000 : ℝ)^8251 ≤ (5320658750009/12500000000000 : ℝ)^6203 := by
    have hnat : (2630864163 : ℕ)^8251*12500000000000^6203 ≤ 5320658750009^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630864163 5000000000 5320658750009 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345679713/10000000000 : ℝ), (-2276264211/10000000000 : ℝ), (2630864163/5000000000 : ℝ)] ![(43470998421637/100000000000000 : ℝ), (6981865782487/50000000000000 : ℝ), (5320658750009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345679713/10000000000 : ℝ)|^8251 ≤ (43470998421637/100000000000000 : ℝ)^6203
        have hw : |(5345679713/10000000000 : ℝ)|=(5345679713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276264211/10000000000 : ℝ)|^8251 ≤ (6981865782487/50000000000000 : ℝ)^6203
        have hw : |(-2276264211/10000000000 : ℝ)|=(2276264211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630864163/5000000000 : ℝ)|^8251 ≤ (5320658750009/12500000000000 : ℝ)^6203
        have hw : |(2630864163/5000000000 : ℝ)|=(2630864163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336419943/2500000000 : ℝ)*x 0 + (328858029/625000000 : ℝ)*x 1 + (-2276263951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336419943/2500000000 : ℝ)^8251 ≤ (5433874882479/12500000000000 : ℝ)^6203 := by
    have hnat : (1336419943 : ℕ)^8251*12500000000000^6203 ≤ 5433874882479^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336419943 2500000000 5433874882479 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328858029/625000000 : ℝ)^8251 ≤ (21282635742509/50000000000000 : ℝ)^6203 := by
    have hnat : (328858029 : ℕ)^8251*50000000000000^6203 ≤ 21282635742509^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328858029 625000000 21282635742509 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276263951/10000000000 : ℝ)^8251 ≤ (6981864721703/50000000000000 : ℝ)^6203 := by
    have hnat : (2276263951 : ℕ)^8251*50000000000000^6203 ≤ 6981864721703^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276263951 10000000000 6981864721703 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336419943/2500000000 : ℝ), (328858029/625000000 : ℝ), (-2276263951/10000000000 : ℝ)] ![(5433874882479/12500000000000 : ℝ), (21282635742509/50000000000000 : ℝ), (6981864721703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336419943/2500000000 : ℝ)|^8251 ≤ (5433874882479/12500000000000 : ℝ)^6203
        have hw : |(1336419943/2500000000 : ℝ)|=(1336419943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328858029/625000000 : ℝ)|^8251 ≤ (21282635742509/50000000000000 : ℝ)^6203
        have hw : |(328858029/625000000 : ℝ)|=(328858029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276263951/10000000000 : ℝ)|^8251 ≤ (6981864721703/50000000000000 : ℝ)^6203
        have hw : |(-2276263951/10000000000 : ℝ)|=(2276263951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094126411/2500000000 : ℝ)*x 0 + (1061492519/2500000000 : ℝ)*x 1 + (4511117211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094126411/2500000000 : ℝ)^8251 ≤ (666302017041/2000000000000 : ℝ)^6203 := by
    have hnat : (1094126411 : ℕ)^8251*2000000000000^6203 ≤ 666302017041^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094126411 2500000000 666302017041 2000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061492519/2500000000 : ℝ)^8251 ≤ (799997721237/2500000000000 : ℝ)^6203 := by
    have hnat : (1061492519 : ℕ)^8251*2500000000000^6203 ≤ 799997721237^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061492519 2500000000 799997721237 2500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511117211/10000000000 : ℝ)^8251 ≤ (8671247570369/25000000000000 : ℝ)^6203 := by
    have hnat : (4511117211 : ℕ)^8251*25000000000000^6203 ≤ 8671247570369^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511117211 10000000000 8671247570369 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094126411/2500000000 : ℝ), (1061492519/2500000000 : ℝ), (4511117211/10000000000 : ℝ)] ![(666302017041/2000000000000 : ℝ), (799997721237/2500000000000 : ℝ), (8671247570369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094126411/2500000000 : ℝ)|^8251 ≤ (666302017041/2000000000000 : ℝ)^6203
        have hw : |(1094126411/2500000000 : ℝ)|=(1094126411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061492519/2500000000 : ℝ)|^8251 ≤ (799997721237/2500000000000 : ℝ)^6203
        have hw : |(1061492519/2500000000 : ℝ)|=(1061492519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511117211/10000000000 : ℝ)|^8251 ≤ (8671247570369/25000000000000 : ℝ)^6203
        have hw : |(4511117211/10000000000 : ℝ)|=(4511117211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441495269/2000000000 : ℝ)*x 0 + (657760197/1250000000 : ℝ)*x 1 + (5396878117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441495269/2000000000 : ℝ)^8251 ≤ (6702625157953/50000000000000 : ℝ)^6203 := by
    have hnat : (441495269 : ℕ)^8251*50000000000000^6203 ≤ 6702625157953^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441495269 2000000000 6702625157953 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657760197/1250000000 : ℝ)^8251 ≤ (42569071182923/100000000000000 : ℝ)^6203 := by
    have hnat : (657760197 : ℕ)^8251*100000000000000^6203 ≤ 42569071182923^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657760197 1250000000 42569071182923 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396878117/10000000000 : ℝ)^8251 ≤ (1375802452713/3125000000000 : ℝ)^6203 := by
    have hnat : (5396878117 : ℕ)^8251*3125000000000^6203 ≤ 1375802452713^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396878117 10000000000 1375802452713 3125000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441495269/2000000000 : ℝ), (657760197/1250000000 : ℝ), (5396878117/10000000000 : ℝ)] ![(6702625157953/50000000000000 : ℝ), (42569071182923/100000000000000 : ℝ), (1375802452713/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441495269/2000000000 : ℝ)|^8251 ≤ (6702625157953/50000000000000 : ℝ)^6203
        have hw : |(-441495269/2000000000 : ℝ)|=(441495269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657760197/1250000000 : ℝ)|^8251 ≤ (42569071182923/100000000000000 : ℝ)^6203
        have hw : |(657760197/1250000000 : ℝ)|=(657760197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396878117/10000000000 : ℝ)|^8251 ≤ (1375802452713/3125000000000 : ℝ)^6203
        have hw : |(5396878117/10000000000 : ℝ)|=(5396878117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311571111/10000000000 : ℝ)*x 0 + (-428222873/2000000000 : ℝ)*x 1 + (2698439087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311571111/10000000000 : ℝ)^8251 ≤ (10775609846913/25000000000000 : ℝ)^6203 := by
    have hnat : (5311571111 : ℕ)^8251*25000000000000^6203 ≤ 10775609846913^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311571111 10000000000 10775609846913 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428222873/2000000000 : ℝ)^8251 ≤ (12871881488457/100000000000000 : ℝ)^6203 := by
    have hnat : (428222873 : ℕ)^8251*100000000000000^6203 ≤ 12871881488457^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428222873 2000000000 12871881488457 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698439087/5000000000 : ℝ)^8251 ≤ (44025679105321/100000000000000 : ℝ)^6203 := by
    have hnat : (2698439087 : ℕ)^8251*100000000000000^6203 ≤ 44025679105321^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698439087 5000000000 44025679105321 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311571111/10000000000 : ℝ), (-428222873/2000000000 : ℝ), (2698439087/5000000000 : ℝ)] ![(10775609846913/25000000000000 : ℝ), (12871881488457/100000000000000 : ℝ), (44025679105321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311571111/10000000000 : ℝ)|^8251 ≤ (10775609846913/25000000000000 : ℝ)^6203
        have hw : |(5311571111/10000000000 : ℝ)|=(5311571111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428222873/2000000000 : ℝ)|^8251 ≤ (12871881488457/100000000000000 : ℝ)^6203
        have hw : |(-428222873/2000000000 : ℝ)|=(428222873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698439087/5000000000 : ℝ)|^8251 ≤ (44025679105321/100000000000000 : ℝ)^6203
        have hw : |(2698439087/5000000000 : ℝ)|=(2698439087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311571081/10000000000 : ℝ)*x 0 + (5396878181/10000000000 : ℝ)*x 1 + (-535278599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311571081/10000000000 : ℝ)^8251 ≤ (43102439063831/100000000000000 : ℝ)^6203 := by
    have hnat : (5311571081 : ℕ)^8251*100000000000000^6203 ≤ 43102439063831^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311571081 10000000000 43102439063831 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396878181/10000000000 : ℝ)^8251 ≤ (22012839590639/50000000000000 : ℝ)^6203 := by
    have hnat : (5396878181 : ℕ)^8251*50000000000000^6203 ≤ 22012839590639^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396878181 10000000000 22012839590639 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535278599/2500000000 : ℝ)^8251 ≤ (12871881736353/100000000000000 : ℝ)^6203 := by
    have hnat : (535278599 : ℕ)^8251*100000000000000^6203 ≤ 12871881736353^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535278599 2500000000 12871881736353 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311571081/10000000000 : ℝ), (5396878181/10000000000 : ℝ), (-535278599/2500000000 : ℝ)] ![(43102439063831/100000000000000 : ℝ), (22012839590639/50000000000000 : ℝ), (12871881736353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311571081/10000000000 : ℝ)|^8251 ≤ (43102439063831/100000000000000 : ℝ)^6203
        have hw : |(5311571081/10000000000 : ℝ)|=(5311571081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396878181/10000000000 : ℝ)|^8251 ≤ (22012839590639/50000000000000 : ℝ)^6203
        have hw : |(5396878181/10000000000 : ℝ)|=(5396878181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535278599/2500000000 : ℝ)|^8251 ≤ (12871881736353/100000000000000 : ℝ)^6203
        have hw : |(-535278599/2500000000 : ℝ)|=(535278599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s5_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376516933/10000000000 : ℝ)*x 0 + (4510426417/10000000000 : ℝ)*x 1 + (2123331693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376516933/10000000000 : ℝ)^8251 ≤ (16657607579693/50000000000000 : ℝ)^6203 := by
    have hnat : (4376516933 : ℕ)^8251*50000000000000^6203 ≤ 16657607579693^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376516933 10000000000 16657607579693 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510426417/10000000000 : ℝ)^8251 ≤ (433474068523/1250000000000 : ℝ)^6203 := by
    have hnat : (4510426417 : ℕ)^8251*1250000000000^6203 ≤ 433474068523^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510426417 10000000000 433474068523 1250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123331693/5000000000 : ℝ)^8251 ≤ (8001714836333/25000000000000 : ℝ)^6203 := by
    have hnat : (2123331693 : ℕ)^8251*25000000000000^6203 ≤ 8001714836333^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123331693 5000000000 8001714836333 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376516933/10000000000 : ℝ), (4510426417/10000000000 : ℝ), (2123331693/5000000000 : ℝ)] ![(16657607579693/50000000000000 : ℝ), (433474068523/1250000000000 : ℝ), (8001714836333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376516933/10000000000 : ℝ)|^8251 ≤ (16657607579693/50000000000000 : ℝ)^6203
        have hw : |(4376516933/10000000000 : ℝ)|=(4376516933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510426417/10000000000 : ℝ)|^8251 ≤ (433474068523/1250000000000 : ℝ)^6203
        have hw : |(4510426417/10000000000 : ℝ)|=(4510426417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123331693/5000000000 : ℝ)|^8251 ≤ (8001714836333/25000000000000 : ℝ)^6203
        have hw : |(2123331693/5000000000 : ℝ)|=(2123331693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2237/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/20000 : ℝ) ^ (4125/1024 : ℝ) ≤ (3444750143127319/25000000000000000000 : ℝ) := by
    have hpowers : (2201/20000 : ℝ)^4125 ≤ (3444750143127319/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^4125*25000000000000000000^1024 ≤ 3444750143127319^1024*20000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 20000 3444750143127319 25000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/20000 : ℝ)) (X := (3444750143127319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2849/20000 : ℝ) ^ (4125/1024 : ℝ) ≤ (38965591254648487/100000000000000000000 : ℝ) := by
    have hpowers : (2849/20000 : ℝ)^4125 ≤ (38965591254648487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2849 : ℕ)^4125*100000000000000000000^1024 ≤ 38965591254648487^1024*20000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 20000 38965591254648487 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/20000 : ℝ)) (X := (38965591254648487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503444750143127319/12500000000000000000 : ℝ) ≤ (10000684035649599/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (12503444750143127319/12500000000000000000 : ℝ)^1024 ≤ (10000684035649599/10000000000000000 : ℝ)^4125 := by
      have hnat : (12503444750143127319 : ℕ)^1024*10000000000000000^4125 ≤ 10000684035649599^4125*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503444750143127319 12500000000000000000 10000684035649599 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684035649599/10000000000000000 : ℝ)) (X := (12503444750143127319/12500000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052744591827157763/100000000000000000000 : ℝ) ≤ (2000261817005789/2000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (100052744591827157763/100000000000000000000 : ℝ)^1024 ≤ (2000261817005789/2000000000000000 : ℝ)^4125 := by
      have hnat : (100052744591827157763 : ℕ)^1024*2000000000000000^4125 ≤ 2000261817005789^4125*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052744591827157763 100000000000000000000 2000261817005789 2000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000261817005789/2000000000000000 : ℝ)) (X := (100052744591827157763/100000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038965591254648487/50000000000000000000 : ℝ) ≤ (10001934134408291/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50038965591254648487/50000000000000000000 : ℝ)^1024 ≤ (10001934134408291/10000000000000000 : ℝ)^4125 := by
      have hnat : (50038965591254648487 : ℕ)^1024*10000000000000000^4125 ≤ 10001934134408291^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038965591254648487 50000000000000000000 10001934134408291 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001934134408291/10000000000000000 : ℝ)) (X := (50038965591254648487/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3444750143127319/25000000000000000000 : ℝ) ≤ ((323884589386652953/324000000000000000 : ℝ)+2*(312524689673/162000000000000 : ℝ)*(2201/20000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (323884589386652953/324000000000000000 : ℝ)+2*(312524689673/162000000000000 : ℝ)*(2201/20000 : ℝ)=(10000684035649599/10000000000000000 : ℝ) by norm_num, show 1+2*(3444750143127319/25000000000000000000 : ℝ)=(12503444750143127319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38965591254648487/100000000000000000000 : ℝ)+(3444750143127319/25000000000000000000 : ℝ) ≤ ((323884589386652953/324000000000000000 : ℝ)+(312524689673/162000000000000 : ℝ)*((2849/20000 : ℝ)+(2201/20000 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (323884589386652953/324000000000000000 : ℝ)+(312524689673/162000000000000 : ℝ)*((2849/20000 : ℝ)+(2201/20000 : ℝ))=(2000261817005789/2000000000000000 : ℝ) by norm_num, show 1+(38965591254648487/100000000000000000000 : ℝ)+(3444750143127319/25000000000000000000 : ℝ)=(100052744591827157763/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38965591254648487/100000000000000000000 : ℝ) ≤ ((323884589386652953/324000000000000000 : ℝ)+2*(312524689673/162000000000000 : ℝ)*(2849/20000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (323884589386652953/324000000000000000 : ℝ)+2*(312524689673/162000000000000 : ℝ)*(2849/20000 : ℝ)=(10001934134408291/10000000000000000 : ℝ) by norm_num, show 1+2*(38965591254648487/100000000000000000000 : ℝ)=(50038965591254648487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (323884589386652953/324000000000000000 : ℝ)*(X 1 0+X 2 0)+(312524689673/162000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (323884589386652953/324000000000000000 : ℝ)) (alpha := (312524689673/162000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (323884589386652953/324000000000000000 : ℝ)*(X 0 1+X 2 1)+(312524689673/162000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (323884589386652953/324000000000000000 : ℝ)) (alpha := (312524689673/162000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (323884589386652953/324000000000000000 : ℝ)*(X 0 2+X 1 2)+(312524689673/162000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (323884589386652953/324000000000000000 : ℝ)) (alpha := (312524689673/162000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2207470559/10000000000 : ℝ)*X 0 0+(674654071/1250000000 : ℝ)*X 0 1+(657716061/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345679713/10000000000 : ℝ)*X 1 0+(-2276264211/10000000000 : ℝ)*X 1 1+(2630864163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336419943/2500000000 : ℝ)*X 2 0+(328858029/625000000 : ℝ)*X 2 1+(-2276263951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094126411/2500000000 : ℝ)*X 0 0+(1061492519/2500000000 : ℝ)*X 0 1+(4511117211/10000000000 : ℝ)*X 0 2+(1094126411/2500000000 : ℝ)*X 1 0+(1061492519/2500000000 : ℝ)*X 1 1+(4511117211/10000000000 : ℝ)*X 1 2+(1094126411/2500000000 : ℝ)*X 2 0+(1061492519/2500000000 : ℝ)*X 2 1+(4511117211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441495269/2000000000 : ℝ)*X 0 0+(657760197/1250000000 : ℝ)*X 0 1+(5396878117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311571111/10000000000 : ℝ)*X 1 0+(-428222873/2000000000 : ℝ)*X 1 1+(2698439087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311571081/10000000000 : ℝ)*X 2 0+(5396878181/10000000000 : ℝ)*X 2 1+(-535278599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376516933/10000000000 : ℝ)*X 0 0+(4510426417/10000000000 : ℝ)*X 0 1+(2123331693/5000000000 : ℝ)*X 0 2+(4376516933/10000000000 : ℝ)*X 1 0+(4510426417/10000000000 : ℝ)*X 1 1+(2123331693/5000000000 : ℝ)*X 1 2+(4376516933/10000000000 : ℝ)*X 2 0+(4510426417/10000000000 : ℝ)*X 2 1+(2123331693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25528152547780914925242577/2700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2120808651/100000000000000 : ℝ)*(base19) + (211186469/10000000000000 : ℝ)*(base23) + (24161459/50000000000000 : ℝ)*(lower2) + (16057631/100000000000000 : ℝ)*(upper3) + (71491291/20000000000000 : ℝ)*(upper5) + (5575752698515009/100000000000000 : ℝ)*(major0) + (5575752698515009/100000000000000 : ℝ)*(major1) + (5575752698515009/100000000000000 : ℝ)*(major2) + (7379897580899777/100000000000000 : ℝ)*(sp0) + (3689979890094697/50000000000000 : ℝ)*(sp1) + (1475991957826671/20000000000000 : ℝ)*(sp2) + (377151982458031/10000000000000 : ℝ)*(sp3) + (64320098267/100000000000000 : ℝ)*(sp4) + (11678144639/50000000000000 : ℝ)*(sp7) + (942885795217397/25000000000000 : ℝ)*(f.failure) + (1475992380199609/20000000000000 : ℝ)*(f.sum) + (42172424101543/8100000000000000000000000000 : ℝ)*base66 + (42360258744814423/32400000000000000000000000000000 : ℝ)*base68 + (81863462839585577/32400000000000000000000000000000 : ℝ)*base69 + (502480801577614423/32400000000000000000000000000000 : ℝ)*base72 + (32222610750857/8100000000000000000000000000 : ℝ)*base73 + (121573027700014423/32400000000000000000000000000000 : ℝ)*base76 + (451626770448814423/32400000000000000000000000000000 : ℝ)*base78 + (477710977925614423/32400000000000000000000000000000 : ℝ)*base80 + (14284533613243/8100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2971339/500000000000000000000 : ℝ)*base89 + (2971339/500000000000000000000 : ℝ)*base91 + (2971339/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1632160791262234219869529/600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734750567/100000000000000 : ℝ)*(base19) + (11186543/1562500000000 : ℝ)*(base23) + (13747807/100000000000000 : ℝ)*(upper2) + (24226073/25000000000000 : ℝ)*(upper3) + (18195249/25000000000000 : ℝ)*(upper5) + (5604934051769463/100000000000000 : ℝ)*(major0) + (5604934051769463/100000000000000 : ℝ)*(major1) + (5604934051769463/100000000000000 : ℝ)*(major2) + (2098384049/10000000000000 : ℝ)*(sp1) + (20548682233/100000000000000 : ℝ)*(sp2) + (1854646505016327/25000000000000 : ℝ)*(sp4) + (7418564301474251/100000000000000 : ℝ)*(sp5) + (1854641188861081/25000000000000 : ℝ)*(sp6) + (379128199279801/10000000000000 : ℝ)*(sp7) + (379128199279801/10000000000000 : ℝ)*(f.failure) + (1854646505016327/25000000000000 : ℝ)*(f.sum) + (4739195123489/900000000000000000000000000 : ℝ)*base66 + (20433338474647529/3600000000000000000000000000000 : ℝ)*base68 + (40595188780552471/3600000000000000000000000000000 : ℝ)*base69 + (5524281586552471/3600000000000000000000000000000 : ℝ)*base71 + (4547537508989/900000000000000000000000000 : ℝ)*base74 + (33080000219752471/3600000000000000000000000000000 : ℝ)*base75 + (11554487186152471/3600000000000000000000000000000 : ℝ)*base77 + (66079572127447529/3600000000000000000000000000000 : ℝ)*base80 + (942390663811/900000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (569913/200000000000000000000 : ℝ)*base90 + (569913/200000000000000000000 : ℝ)*base92 + (569913/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1058_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1058_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1058_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1058_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
