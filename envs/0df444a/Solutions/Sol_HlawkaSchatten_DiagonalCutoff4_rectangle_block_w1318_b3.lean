-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:54.107818+00:00
-- url     : https://prove2.me/submissions/6a87bb37-75d1-4e2a-879f-631183bc628a

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
theorem support_rectangle_w1318_box_0 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-59240881/312500000 : ℝ)*x 0 + (5390937287/10000000000 : ℝ)*x 1 + (2695468593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59240881/312500000 : ℝ)^2139 ≤ (2808236529471/25000000000000 : ℝ)^1627 := by
    have hnat : (59240881 : ℕ)^2139*25000000000000^1627 ≤ 2808236529471^1627*312500000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59240881 312500000 2808236529471 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390937287/10000000000 : ℝ)^2139 ≤ (44383527477987/100000000000000 : ℝ)^1627 := by
    have hnat : (5390937287 : ℕ)^2139*100000000000000^1627 ≤ 44383527477987^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390937287 10000000000 44383527477987 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695468593/5000000000 : ℝ)^2139 ≤ (44383526384781/100000000000000 : ℝ)^1627 := by
    have hnat : (2695468593 : ℕ)^2139*100000000000000^1627 ≤ 44383526384781^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695468593 5000000000 44383526384781 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59240881/312500000 : ℝ), (5390937287/10000000000 : ℝ), (2695468593/5000000000 : ℝ)] ![(2808236529471/25000000000000 : ℝ), (44383527477987/100000000000000 : ℝ), (44383526384781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59240881/312500000 : ℝ)|^2139 ≤ (2808236529471/25000000000000 : ℝ)^1627
        have hw : |(-59240881/312500000 : ℝ)|=(59240881/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390937287/10000000000 : ℝ)|^2139 ≤ (44383527477987/100000000000000 : ℝ)^1627
        have hw : |(5390937287/10000000000 : ℝ)|=(5390937287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695468593/5000000000 : ℝ)|^2139 ≤ (44383526384781/100000000000000 : ℝ)^1627
        have hw : |(2695468593/5000000000 : ℝ)|=(2695468593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_1 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (105696223/200000000 : ℝ)*x 0 + (-2040980909/10000000000 : ℝ)*x 1 + (2695468923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105696223/200000000 : ℝ)^2139 ≤ (43238410925563/100000000000000 : ℝ)^1627 := by
    have hnat : (105696223 : ℕ)^2139*100000000000000^1627 ≤ 43238410925563^1627*200000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105696223 200000000 43238410925563 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040980909/10000000000 : ℝ)^2139 ≤ (12378055523389/100000000000000 : ℝ)^1627 := by
    have hnat : (2040980909 : ℕ)^2139*100000000000000^1627 ≤ 12378055523389^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040980909 10000000000 12378055523389 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695468923/5000000000 : ℝ)^2139 ≤ (22191766764253/50000000000000 : ℝ)^1627 := by
    have hnat : (2695468923 : ℕ)^2139*50000000000000^1627 ≤ 22191766764253^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695468923 5000000000 22191766764253 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105696223/200000000 : ℝ), (-2040980909/10000000000 : ℝ), (2695468923/5000000000 : ℝ)] ![(43238410925563/100000000000000 : ℝ), (12378055523389/100000000000000 : ℝ), (22191766764253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105696223/200000000 : ℝ)|^2139 ≤ (43238410925563/100000000000000 : ℝ)^1627
        have hw : |(105696223/200000000 : ℝ)|=(105696223/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040980909/10000000000 : ℝ)|^2139 ≤ (12378055523389/100000000000000 : ℝ)^1627
        have hw : |(-2040980909/10000000000 : ℝ)|=(2040980909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695468923/5000000000 : ℝ)|^2139 ≤ (22191766764253/50000000000000 : ℝ)^1627
        have hw : |(2695468923/5000000000 : ℝ)|=(2695468923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_2 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1056962337/2000000000 : ℝ)*x 0 + (539093753/1000000000 : ℝ)*x 1 + (-255122577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056962337/2000000000 : ℝ)^2139 ≤ (43238416680191/100000000000000 : ℝ)^1627 := by
    have hnat : (1056962337 : ℕ)^2139*100000000000000^1627 ≤ 43238416680191^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056962337 2000000000 43238416680191 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539093753/1000000000 : ℝ)^2139 ≤ (44383530108177/100000000000000 : ℝ)^1627 := by
    have hnat : (539093753 : ℕ)^2139*100000000000000^1627 ≤ 44383530108177^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539093753 1000000000 44383530108177 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255122577/1250000000 : ℝ)^2139 ≤ (618902659361/5000000000000 : ℝ)^1627 := by
    have hnat : (255122577 : ℕ)^2139*5000000000000^1627 ≤ 618902659361^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255122577 1250000000 618902659361 5000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056962337/2000000000 : ℝ), (539093753/1000000000 : ℝ), (-255122577/1250000000 : ℝ)] ![(43238416680191/100000000000000 : ℝ), (44383530108177/100000000000000 : ℝ), (618902659361/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056962337/2000000000 : ℝ)|^2139 ≤ (43238416680191/100000000000000 : ℝ)^1627
        have hw : |(1056962337/2000000000 : ℝ)|=(1056962337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539093753/1000000000 : ℝ)|^2139 ≤ (44383530108177/100000000000000 : ℝ)^1627
        have hw : |(539093753/1000000000 : ℝ)|=(539093753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255122577/1250000000 : ℝ)|^2139 ≤ (618902659361/5000000000000 : ℝ)^1627
        have hw : |(-255122577/1250000000 : ℝ)|=(255122577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_3 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1120424877/2500000000 : ℝ)*x 0 + (426249947/1000000000 : ℝ)*x 1 + (1065624889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120424877/2500000000 : ℝ)^2139 ≤ (1740705845237/5000000000000 : ℝ)^1627 := by
    have hnat : (1120424877 : ℕ)^2139*5000000000000^1627 ≤ 1740705845237^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120424877 2500000000 1740705845237 5000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426249947/1000000000 : ℝ)^2139 ≤ (20370588193/62500000000 : ℝ)^1627 := by
    have hnat : (426249947 : ℕ)^2139*62500000000^1627 ≤ 20370588193^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426249947 1000000000 20370588193 62500000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065624889/2500000000 : ℝ)^2139 ≤ (8148235493333/25000000000000 : ℝ)^1627 := by
    have hnat : (1065624889 : ℕ)^2139*25000000000000^1627 ≤ 8148235493333^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065624889 2500000000 8148235493333 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120424877/2500000000 : ℝ), (426249947/1000000000 : ℝ), (1065624889/2500000000 : ℝ)] ![(1740705845237/5000000000000 : ℝ), (20370588193/62500000000 : ℝ), (8148235493333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120424877/2500000000 : ℝ)|^2139 ≤ (1740705845237/5000000000000 : ℝ)^1627
        have hw : |(1120424877/2500000000 : ℝ)|=(1120424877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(426249947/1000000000 : ℝ)|^2139 ≤ (20370588193/62500000000 : ℝ)^1627
        have hw : |(426249947/1000000000 : ℝ)|=(426249947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1065624889/2500000000 : ℝ)|^2139 ≤ (8148235493333/25000000000000 : ℝ)^1627
        have hw : |(1065624889/2500000000 : ℝ)|=(1065624889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_4 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-559207379/2500000000 : ℝ)*x 0 + (5264368117/10000000000 : ℝ)*x 1 + (1316092103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559207379/2500000000 : ℝ)^2139 ≤ (349067260663/2500000000000 : ℝ)^1627 := by
    have hnat : (559207379 : ℕ)^2139*2500000000000^1627 ≤ 349067260663^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559207379 2500000000 349067260663 2500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264368117/10000000000 : ℝ)^2139 ≤ (10754663298303/25000000000000 : ℝ)^1627 := by
    have hnat : (5264368117 : ℕ)^2139*25000000000000^1627 ≤ 10754663298303^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264368117 10000000000 10754663298303 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316092103/2500000000 : ℝ)^2139 ≤ (43018656362457/100000000000000 : ℝ)^1627 := by
    have hnat : (1316092103 : ℕ)^2139*100000000000000^1627 ≤ 43018656362457^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316092103 2500000000 43018656362457 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559207379/2500000000 : ℝ), (5264368117/10000000000 : ℝ), (1316092103/2500000000 : ℝ)] ![(349067260663/2500000000000 : ℝ), (10754663298303/25000000000000 : ℝ), (43018656362457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559207379/2500000000 : ℝ)|^2139 ≤ (349067260663/2500000000000 : ℝ)^1627
        have hw : |(-559207379/2500000000 : ℝ)|=(559207379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264368117/10000000000 : ℝ)|^2139 ≤ (10754663298303/25000000000000 : ℝ)^1627
        have hw : |(5264368117/10000000000 : ℝ)|=(5264368117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316092103/2500000000 : ℝ)|^2139 ≤ (43018656362457/100000000000000 : ℝ)^1627
        have hw : |(1316092103/2500000000 : ℝ)|=(1316092103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_5 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214952083/400000000 : ℝ)*x 0 + (-1045798187/5000000000 : ℝ)*x 1 + (1316092089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214952083/400000000 : ℝ)^2139 ≤ (44198151764193/100000000000000 : ℝ)^1627 := by
    have hnat : (214952083 : ℕ)^2139*100000000000000^1627 ≤ 44198151764193^1627*400000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214952083 400000000 44198151764193 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045798187/5000000000 : ℝ)^2139 ≤ (12783192458399/100000000000000 : ℝ)^1627 := by
    have hnat : (1045798187 : ℕ)^2139*100000000000000^1627 ≤ 12783192458399^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045798187 5000000000 12783192458399 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316092089/2500000000 : ℝ)^2139 ≤ (21509327880419/50000000000000 : ℝ)^1627 := by
    have hnat : (1316092089 : ℕ)^2139*50000000000000^1627 ≤ 21509327880419^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316092089 2500000000 21509327880419 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214952083/400000000 : ℝ), (-1045798187/5000000000 : ℝ), (1316092089/2500000000 : ℝ)] ![(44198151764193/100000000000000 : ℝ), (12783192458399/100000000000000 : ℝ), (21509327880419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214952083/400000000 : ℝ)|^2139 ≤ (44198151764193/100000000000000 : ℝ)^1627
        have hw : |(214952083/400000000 : ℝ)|=(214952083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045798187/5000000000 : ℝ)|^2139 ≤ (12783192458399/100000000000000 : ℝ)^1627
        have hw : |(-1045798187/5000000000 : ℝ)|=(1045798187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316092089/2500000000 : ℝ)|^2139 ≤ (21509327880419/50000000000000 : ℝ)^1627
        have hw : |(1316092089/2500000000 : ℝ)|=(1316092089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_6 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5373802177/10000000000 : ℝ)*x 0 + (5264368207/10000000000 : ℝ)*x 1 + (-2091596437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373802177/10000000000 : ℝ)^2139 ≤ (22099076433559/50000000000000 : ℝ)^1627 := by
    have hnat : (5373802177 : ℕ)^2139*50000000000000^1627 ≤ 22099076433559^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373802177 10000000000 22099076433559 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264368207/10000000000 : ℝ)^2139 ≤ (43018654160101/100000000000000 : ℝ)^1627 := by
    have hnat : (5264368207 : ℕ)^2139*100000000000000^1627 ≤ 43018654160101^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264368207 10000000000 43018654160101 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091596437/10000000000 : ℝ)^2139 ≤ (12783192964603/100000000000000 : ℝ)^1627 := by
    have hnat : (2091596437 : ℕ)^2139*100000000000000^1627 ≤ 12783192964603^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091596437 10000000000 12783192964603 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373802177/10000000000 : ℝ), (5264368207/10000000000 : ℝ), (-2091596437/10000000000 : ℝ)] ![(22099076433559/50000000000000 : ℝ), (43018654160101/100000000000000 : ℝ), (12783192964603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373802177/10000000000 : ℝ)|^2139 ≤ (22099076433559/50000000000000 : ℝ)^1627
        have hw : |(5373802177/10000000000 : ℝ)|=(5373802177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264368207/10000000000 : ℝ)|^2139 ≤ (43018654160101/100000000000000 : ℝ)^1627
        have hw : |(5264368207/10000000000 : ℝ)|=(5264368207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091596437/10000000000 : ℝ)|^2139 ≤ (12783192964603/100000000000000 : ℝ)^1627
        have hw : |(-2091596437/10000000000 : ℝ)|=(2091596437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_7 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4183285003/10000000000 : ℝ)*x 0 + (551456541/1250000000 : ℝ)*x 1 + (441165237/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183285003/10000000000 : ℝ)^2139 ≤ (31798960824673/100000000000000 : ℝ)^1627 := by
    have hnat : (4183285003 : ℕ)^2139*100000000000000^1627 ≤ 31798960824673^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183285003 10000000000 31798960824673 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551456541/1250000000 : ℝ)^2139 ≤ (4262564921437/12500000000000 : ℝ)^1627 := by
    have hnat : (551456541 : ℕ)^2139*12500000000000^1627 ≤ 4262564921437^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551456541 1250000000 4262564921437 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441165237/1000000000 : ℝ)^2139 ≤ (1065641243697/3125000000000 : ℝ)^1627 := by
    have hnat : (441165237 : ℕ)^2139*3125000000000^1627 ≤ 1065641243697^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441165237 1000000000 1065641243697 3125000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183285003/10000000000 : ℝ), (551456541/1250000000 : ℝ), (441165237/1000000000 : ℝ)] ![(31798960824673/100000000000000 : ℝ), (4262564921437/12500000000000 : ℝ), (1065641243697/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183285003/10000000000 : ℝ)|^2139 ≤ (31798960824673/100000000000000 : ℝ)^1627
        have hw : |(4183285003/10000000000 : ℝ)|=(4183285003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551456541/1250000000 : ℝ)|^2139 ≤ (4262564921437/12500000000000 : ℝ)^1627
        have hw : |(551456541/1250000000 : ℝ)|=(551456541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441165237/1000000000 : ℝ)|^2139 ≤ (1065641243697/3125000000000 : ℝ)^1627
        have hw : |(441165237/1000000000 : ℝ)|=(441165237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_8 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165259627/10000000000 : ℝ)*x 0 + (1294337291/2500000000 : ℝ)*x 1 + (675620813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165259627/10000000000 : ℝ)^2139 ≤ (6689164478749/50000000000000 : ℝ)^1627 := by
    have hnat : (2165259627 : ℕ)^2139*50000000000000^1627 ≤ 6689164478749^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165259627 10000000000 6689164478749 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294337291/2500000000 : ℝ)^2139 ≤ (5260778950727/12500000000000 : ℝ)^1627 := by
    have hnat : (1294337291 : ℕ)^2139*12500000000000^1627 ≤ 5260778950727^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294337291 2500000000 5260778950727 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675620813/1250000000 : ℝ)^2139 ≤ (5566929926329/12500000000000 : ℝ)^1627 := by
    have hnat : (675620813 : ℕ)^2139*12500000000000^1627 ≤ 5566929926329^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675620813 1250000000 5566929926329 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165259627/10000000000 : ℝ), (1294337291/2500000000 : ℝ), (675620813/1250000000 : ℝ)] ![(6689164478749/50000000000000 : ℝ), (5260778950727/12500000000000 : ℝ), (5566929926329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165259627/10000000000 : ℝ)|^2139 ≤ (6689164478749/50000000000000 : ℝ)^1627
        have hw : |(-2165259627/10000000000 : ℝ)|=(2165259627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294337291/2500000000 : ℝ)|^2139 ≤ (5260778950727/12500000000000 : ℝ)^1627
        have hw : |(1294337291/2500000000 : ℝ)|=(1294337291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675620813/1250000000 : ℝ)|^2139 ≤ (5566929926329/12500000000000 : ℝ)^1627
        have hw : |(675620813/1250000000 : ℝ)|=(675620813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_9 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274942617/10000000000 : ℝ)*x 0 + (-127202293/625000000 : ℝ)*x 1 + (5404965759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274942617/10000000000 : ℝ)^2139 ≤ (10783073271149/25000000000000 : ℝ)^1627 := by
    have hnat : (5274942617 : ℕ)^2139*25000000000000^1627 ≤ 10783073271149^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274942617 10000000000 10783073271149 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127202293/625000000 : ℝ)^2139 ≤ (616613778387/5000000000000 : ℝ)^1627 := by
    have hnat : (127202293 : ℕ)^2139*5000000000000^1627 ≤ 616613778387^1627*625000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127202293 625000000 616613778387 5000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404965759/10000000000 : ℝ)^2139 ≤ (8907086268057/20000000000000 : ℝ)^1627 := by
    have hnat : (5404965759 : ℕ)^2139*20000000000000^1627 ≤ 8907086268057^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404965759 10000000000 8907086268057 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274942617/10000000000 : ℝ), (-127202293/625000000 : ℝ), (5404965759/10000000000 : ℝ)] ![(10783073271149/25000000000000 : ℝ), (616613778387/5000000000000 : ℝ), (8907086268057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274942617/10000000000 : ℝ)|^2139 ≤ (10783073271149/25000000000000 : ℝ)^1627
        have hw : |(5274942617/10000000000 : ℝ)|=(5274942617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127202293/625000000 : ℝ)|^2139 ≤ (616613778387/5000000000000 : ℝ)^1627
        have hw : |(-127202293/625000000 : ℝ)|=(127202293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404965759/10000000000 : ℝ)|^2139 ≤ (8907086268057/20000000000000 : ℝ)^1627
        have hw : |(5404965759/10000000000 : ℝ)|=(5404965759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_10 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1054988509/2000000000 : ℝ)*x 0 + (2702483047/5000000000 : ℝ)*x 1 + (-254404541/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054988509/2000000000 : ℝ)^2139 ≤ (43132292310597/100000000000000 : ℝ)^1627 := by
    have hnat : (1054988509 : ℕ)^2139*100000000000000^1627 ≤ 43132292310597^1627*2000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054988509 2000000000 43132292310597 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702483047/5000000000 : ℝ)^2139 ≤ (44535434969233/100000000000000 : ℝ)^1627 := by
    have hnat : (2702483047 : ℕ)^2139*100000000000000^1627 ≤ 44535434969233^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702483047 5000000000 44535434969233 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254404541/1250000000 : ℝ)^2139 ≤ (6166136349953/50000000000000 : ℝ)^1627 := by
    have hnat : (254404541 : ℕ)^2139*50000000000000^1627 ≤ 6166136349953^1627*1250000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254404541 1250000000 6166136349953 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054988509/2000000000 : ℝ), (2702483047/5000000000 : ℝ), (-254404541/1250000000 : ℝ)] ![(43132292310597/100000000000000 : ℝ), (44535434969233/100000000000000 : ℝ), (6166136349953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054988509/2000000000 : ℝ)|^2139 ≤ (43132292310597/100000000000000 : ℝ)^1627
        have hw : |(1054988509/2000000000 : ℝ)|=(1054988509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702483047/5000000000 : ℝ)|^2139 ≤ (44535434969233/100000000000000 : ℝ)^1627
        have hw : |(2702483047/5000000000 : ℝ)|=(2702483047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254404541/1250000000 : ℝ)|^2139 ≤ (6166136349953/50000000000000 : ℝ)^1627
        have hw : |(-254404541/1250000000 : ℝ)|=(254404541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_11 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2257108023/5000000000 : ℝ)*x 0 + (1061488391/2500000000 : ℝ)*x 1 + (1061488461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257108023/5000000000 : ℝ)^2139 ≤ (35146573437099/100000000000000 : ℝ)^1627 := by
    have hnat : (2257108023 : ℕ)^2139*100000000000000^1627 ≤ 35146573437099^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257108023 5000000000 35146573437099 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061488391/2500000000 : ℝ)^2139 ≤ (32426711865897/100000000000000 : ℝ)^1627 := by
    have hnat : (1061488391 : ℕ)^2139*100000000000000^1627 ≤ 32426711865897^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061488391 2500000000 32426711865897 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061488461/2500000000 : ℝ)^2139 ≤ (4053339334651/12500000000000 : ℝ)^1627 := by
    have hnat : (1061488461 : ℕ)^2139*12500000000000^1627 ≤ 4053339334651^1627*2500000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061488461 2500000000 4053339334651 12500000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257108023/5000000000 : ℝ), (1061488391/2500000000 : ℝ), (1061488461/2500000000 : ℝ)] ![(35146573437099/100000000000000 : ℝ), (32426711865897/100000000000000 : ℝ), (4053339334651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257108023/5000000000 : ℝ)|^2139 ≤ (35146573437099/100000000000000 : ℝ)^1627
        have hw : |(2257108023/5000000000 : ℝ)|=(2257108023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061488391/2500000000 : ℝ)|^2139 ≤ (32426711865897/100000000000000 : ℝ)^1627
        have hw : |(1061488391/2500000000 : ℝ)|=(1061488391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061488461/2500000000 : ℝ)|^2139 ≤ (4053339334651/12500000000000 : ℝ)^1627
        have hw : |(1061488461/2500000000 : ℝ)|=(1061488461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_12 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967662729/10000000000 : ℝ)*x 0 + (2737847837/5000000000 : ℝ)*x 1 + (2626659979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967662729/10000000000 : ℝ)^2139 ≤ (5898400668711/50000000000000 : ℝ)^1627 := by
    have hnat : (1967662729 : ℕ)^2139*50000000000000^1627 ≤ 5898400668711^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967662729 10000000000 5898400668711 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737847837/5000000000 : ℝ)^2139 ≤ (45303198862037/100000000000000 : ℝ)^1627 := by
    have hnat : (2737847837 : ℕ)^2139*100000000000000^1627 ≤ 45303198862037^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737847837 5000000000 45303198862037 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626659979/5000000000 : ℝ)^2139 ≤ (21449999894343/50000000000000 : ℝ)^1627 := by
    have hnat : (2626659979 : ℕ)^2139*50000000000000^1627 ≤ 21449999894343^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626659979 5000000000 21449999894343 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967662729/10000000000 : ℝ), (2737847837/5000000000 : ℝ), (2626659979/5000000000 : ℝ)] ![(5898400668711/50000000000000 : ℝ), (45303198862037/100000000000000 : ℝ), (21449999894343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967662729/10000000000 : ℝ)|^2139 ≤ (5898400668711/50000000000000 : ℝ)^1627
        have hw : |(-1967662729/10000000000 : ℝ)|=(1967662729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737847837/5000000000 : ℝ)|^2139 ≤ (45303198862037/100000000000000 : ℝ)^1627
        have hw : |(2737847837/5000000000 : ℝ)|=(2737847837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626659979/5000000000 : ℝ)|^2139 ≤ (21449999894343/50000000000000 : ℝ)^1627
        have hw : |(2626659979/5000000000 : ℝ)|=(2626659979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_13 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538156713/1000000000 : ℝ)*x 0 + (-209590989/1000000000 : ℝ)*x 1 + (5253320257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538156713/1000000000 : ℝ)^2139 ≤ (1771285371411/4000000000000 : ℝ)^1627 := by
    have hnat : (538156713 : ℕ)^2139*4000000000000^1627 ≤ 1771285371411^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538156713 1000000000 1771285371411 4000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209590989/1000000000 : ℝ)^2139 ≤ (12817862704843/100000000000000 : ℝ)^1627 := by
    have hnat : (209590989 : ℕ)^2139*100000000000000^1627 ≤ 12817862704843^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209590989 1000000000 12817862704843 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253320257/10000000000 : ℝ)^2139 ≤ (42900002998781/100000000000000 : ℝ)^1627 := by
    have hnat : (5253320257 : ℕ)^2139*100000000000000^1627 ≤ 42900002998781^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253320257 10000000000 42900002998781 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538156713/1000000000 : ℝ), (-209590989/1000000000 : ℝ), (5253320257/10000000000 : ℝ)] ![(1771285371411/4000000000000 : ℝ), (12817862704843/100000000000000 : ℝ), (42900002998781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538156713/1000000000 : ℝ)|^2139 ≤ (1771285371411/4000000000000 : ℝ)^1627
        have hw : |(538156713/1000000000 : ℝ)|=(538156713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209590989/1000000000 : ℝ)|^2139 ≤ (12817862704843/100000000000000 : ℝ)^1627
        have hw : |(-209590989/1000000000 : ℝ)|=(209590989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253320257/10000000000 : ℝ)|^2139 ≤ (42900002998781/100000000000000 : ℝ)^1627
        have hw : |(5253320257/10000000000 : ℝ)|=(5253320257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_14 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538156717/1000000000 : ℝ)*x 0 + (525332001/1000000000 : ℝ)*x 1 + (-1047955083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538156717/1000000000 : ℝ)^2139 ≤ (44282134717991/100000000000000 : ℝ)^1627 := by
    have hnat : (538156717 : ℕ)^2139*100000000000000^1627 ≤ 44282134717991^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538156717 1000000000 44282134717991 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525332001/1000000000 : ℝ)^2139 ≤ (42900000346963/100000000000000 : ℝ)^1627 := by
    have hnat : (525332001 : ℕ)^2139*100000000000000^1627 ≤ 42900000346963^1627*1000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525332001 1000000000 42900000346963 100000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047955083/5000000000 : ℝ)^2139 ≤ (2563572984787/20000000000000 : ℝ)^1627 := by
    have hnat : (1047955083 : ℕ)^2139*20000000000000^1627 ≤ 2563572984787^1627*5000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047955083 5000000000 2563572984787 20000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538156717/1000000000 : ℝ), (525332001/1000000000 : ℝ), (-1047955083/5000000000 : ℝ)] ![(44282134717991/100000000000000 : ℝ), (42900000346963/100000000000000 : ℝ), (2563572984787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538156717/1000000000 : ℝ)|^2139 ≤ (44282134717991/100000000000000 : ℝ)^1627
        have hw : |(538156717/1000000000 : ℝ)|=(538156717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525332001/1000000000 : ℝ)|^2139 ≤ (42900000346963/100000000000000 : ℝ)^1627
        have hw : |(525332001/1000000000 : ℝ)|=(525332001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047955083/5000000000 : ℝ)|^2139 ≤ (2563572984787/20000000000000 : ℝ)^1627
        have hw : |(-1047955083/5000000000 : ℝ)|=(1047955083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1318_box_15 (p : ℝ) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4156789043/10000000000 : ℝ)*x 0 + (3456767/7812500 : ℝ)*x 1 + (4424661329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4156789043/10000000000 : ℝ)^2139 ≤ (15767218525657/50000000000000 : ℝ)^1627 := by
    have hnat : (4156789043 : ℕ)^2139*50000000000000^1627 ≤ 15767218525657^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156789043 10000000000 15767218525657 50000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3456767/7812500 : ℝ)^2139 ≤ (8558195915583/25000000000000 : ℝ)^1627 := by
    have hnat : (3456767 : ℕ)^2139*25000000000000^1627 ≤ 8558195915583^1627*7812500^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3456767 7812500 8558195915583 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424661329/10000000000 : ℝ)^2139 ≤ (8558194819603/25000000000000 : ℝ)^1627 := by
    have hnat : (4424661329 : ℕ)^2139*25000000000000^1627 ≤ 8558194819603^1627*10000000000^2139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424661329 10000000000 8558194819603 25000000000000 2139 1627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2139/512 : ℝ)) 2139 1627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4156789043/10000000000 : ℝ), (3456767/7812500 : ℝ), (4424661329/10000000000 : ℝ)] ![(15767218525657/50000000000000 : ℝ), (8558195915583/25000000000000 : ℝ), (8558194819603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4156789043/10000000000 : ℝ)|^2139 ≤ (15767218525657/50000000000000 : ℝ)^1627
        have hw : |(4156789043/10000000000 : ℝ)|=(4156789043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3456767/7812500 : ℝ)|^2139 ≤ (8558195915583/25000000000000 : ℝ)^1627
        have hw : |(3456767/7812500 : ℝ)|=(3456767/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424661329/10000000000 : ℝ)|^2139 ≤ (8558194819603/25000000000000 : ℝ)^1627
        have hw : |(4424661329/10000000000 : ℝ)|=(4424661329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1318_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62847/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11779/20000 : ℝ) ∧ (79813/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42129/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11093/100000 : ℝ) ^ (4277/1024 : ℝ) ≤ (256649849023343/2500000000000000000 : ℝ) := by
    have hpowers : (11093/100000 : ℝ)^4277 ≤ (256649849023343/2500000000000000000 : ℝ)^1024 := by
      have hnat : (11093 : ℕ)^4277*2500000000000000000^1024 ≤ 256649849023343^1024*100000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11093 100000 256649849023343 2500000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11093/100000 : ℝ)) (X := (256649849023343/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1469/10000 : ℝ) ^ (4277/1024 : ℝ) ≤ (8294530082820031/25000000000000000000 : ℝ) := by
    have hpowers : (1469/10000 : ℝ)^4277 ≤ (8294530082820031/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1469 : ℕ)^4277*25000000000000000000^1024 ≤ 8294530082820031^1024*10000^4277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 10000 8294530082820031 25000000000000000000 4277 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/10000 : ℝ)) (X := (8294530082820031/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250256649849023343/1250000000000000000 : ℝ) ≤ (1000049153879341/1000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (1250256649849023343/1250000000000000000 : ℝ)^1024 ≤ (1000049153879341/1000000000000000 : ℝ)^4277 := by
      have hnat : (1250256649849023343 : ℕ)^1024*1000000000000000^4277 ≤ 1000049153879341^4277*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250256649849023343 1250000000000000000 1000049153879341 1000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000049153879341/1000000000000000 : ℝ)) (X := (1250256649849023343/1250000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010861028573053461/25000000000000000000 : ℝ) ≤ (5000519983926691/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (25010861028573053461/25000000000000000000 : ℝ)^1024 ≤ (5000519983926691/5000000000000000 : ℝ)^4277 := by
      have hnat : (25010861028573053461 : ℕ)^1024*5000000000000000^4277 ≤ 5000519983926691^4277*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010861028573053461 25000000000000000000 5000519983926691 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000519983926691/5000000000000000 : ℝ)) (X := (25010861028573053461/25000000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508294530082820031/12500000000000000000 : ℝ) ≤ (5000794198456677/5000000000000000 : ℝ) ^ (4277/1024 : ℝ) := by
    have hpowers : (12508294530082820031/12500000000000000000 : ℝ)^1024 ≤ (5000794198456677/5000000000000000 : ℝ)^4277 := by
      have hnat : (12508294530082820031 : ℕ)^1024*5000000000000000^4277 ≤ 5000794198456677^4277*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508294530082820031 12500000000000000000 5000794198456677 5000000000000000 1024 4277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000794198456677/5000000000000000 : ℝ)) (X := (12508294530082820031/12500000000000000000 : ℝ)) (by norm_num) 4277 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(256649849023343/2500000000000000000 : ℝ) ≤ ((17979800308957678489/17985000000000000000 : ℝ)+2*(137107264993/89925000000000 : ℝ)*(11093/100000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (17979800308957678489/17985000000000000000 : ℝ)+2*(137107264993/89925000000000 : ℝ)*(11093/100000 : ℝ)=(1000049153879341/1000000000000000 : ℝ) by norm_num, show 1+2*(256649849023343/2500000000000000000 : ℝ)=(1250256649849023343/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8294530082820031/25000000000000000000 : ℝ)+(256649849023343/2500000000000000000 : ℝ) ≤ ((17979800308957678489/17985000000000000000 : ℝ)+(137107264993/89925000000000 : ℝ)*((1469/10000 : ℝ)+(11093/100000 : ℝ)))^(4277/1024 : ℝ) := by
    rw [show (17979800308957678489/17985000000000000000 : ℝ)+(137107264993/89925000000000 : ℝ)*((1469/10000 : ℝ)+(11093/100000 : ℝ))=(5000519983926691/5000000000000000 : ℝ) by norm_num, show 1+(8294530082820031/25000000000000000000 : ℝ)+(256649849023343/2500000000000000000 : ℝ)=(25010861028573053461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8294530082820031/25000000000000000000 : ℝ) ≤ ((17979800308957678489/17985000000000000000 : ℝ)+2*(137107264993/89925000000000 : ℝ)*(1469/10000 : ℝ))^(4277/1024 : ℝ) := by
    rw [show (17979800308957678489/17985000000000000000 : ℝ)+2*(137107264993/89925000000000 : ℝ)*(1469/10000 : ℝ)=(5000794198456677/5000000000000000 : ℝ) by norm_num, show 1+2*(8294530082820031/25000000000000000000 : ℝ)=(12508294530082820031/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17979800308957678489/17985000000000000000 : ℝ)*(X 1 0+X 2 0)+(137107264993/89925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (17979800308957678489/17985000000000000000 : ℝ)) (alpha := (137107264993/89925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17979800308957678489/17985000000000000000 : ℝ)*(X 0 1+X 2 1)+(137107264993/89925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (17979800308957678489/17985000000000000000 : ℝ)) (alpha := (137107264993/89925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17979800308957678489/17985000000000000000 : ℝ)*(X 0 2+X 1 2)+(137107264993/89925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4277/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (17979800308957678489/17985000000000000000 : ℝ)) (alpha := (137107264993/89925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-59240881/312500000 : ℝ)*X 0 0+(5390937287/10000000000 : ℝ)*X 0 1+(2695468593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((105696223/200000000 : ℝ)*X 1 0+(-2040980909/10000000000 : ℝ)*X 1 1+(2695468923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056962337/2000000000 : ℝ)*X 2 0+(539093753/1000000000 : ℝ)*X 2 1+(-255122577/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120424877/2500000000 : ℝ)*X 0 0+(426249947/1000000000 : ℝ)*X 0 1+(1065624889/2500000000 : ℝ)*X 0 2+(1120424877/2500000000 : ℝ)*X 1 0+(426249947/1000000000 : ℝ)*X 1 1+(1065624889/2500000000 : ℝ)*X 1 2+(1120424877/2500000000 : ℝ)*X 2 0+(426249947/1000000000 : ℝ)*X 2 1+(1065624889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-559207379/2500000000 : ℝ)*X 0 0+(5264368117/10000000000 : ℝ)*X 0 1+(1316092103/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((214952083/400000000 : ℝ)*X 1 0+(-1045798187/5000000000 : ℝ)*X 1 1+(1316092089/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373802177/10000000000 : ℝ)*X 2 0+(5264368207/10000000000 : ℝ)*X 2 1+(-2091596437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183285003/10000000000 : ℝ)*X 0 0+(551456541/1250000000 : ℝ)*X 0 1+(441165237/1000000000 : ℝ)*X 0 2+(4183285003/10000000000 : ℝ)*X 1 0+(551456541/1250000000 : ℝ)*X 1 1+(441165237/1000000000 : ℝ)*X 1 2+(4183285003/10000000000 : ℝ)*X 2 0+(551456541/1250000000 : ℝ)*X 2 1+(441165237/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2165259627/10000000000 : ℝ)*X 0 0+(1294337291/2500000000 : ℝ)*X 0 1+(675620813/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274942617/10000000000 : ℝ)*X 1 0+(-127202293/625000000 : ℝ)*X 1 1+(5404965759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1054988509/2000000000 : ℝ)*X 2 0+(2702483047/5000000000 : ℝ)*X 2 1+(-254404541/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2257108023/5000000000 : ℝ)*X 0 0+(1061488391/2500000000 : ℝ)*X 0 1+(1061488461/2500000000 : ℝ)*X 0 2+(2257108023/5000000000 : ℝ)*X 1 0+(1061488391/2500000000 : ℝ)*X 1 1+(1061488461/2500000000 : ℝ)*X 1 2+(2257108023/5000000000 : ℝ)*X 2 0+(1061488391/2500000000 : ℝ)*X 2 1+(1061488461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1967662729/10000000000 : ℝ)*X 0 0+(2737847837/5000000000 : ℝ)*X 0 1+(2626659979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538156713/1000000000 : ℝ)*X 1 0+(-209590989/1000000000 : ℝ)*X 1 1+(5253320257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((538156717/1000000000 : ℝ)*X 2 0+(525332001/1000000000 : ℝ)*X 2 1+(-1047955083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4156789043/10000000000 : ℝ)*X 0 0+(3456767/7812500 : ℝ)*X 0 1+(4424661329/10000000000 : ℝ)*X 0 2+(4156789043/10000000000 : ℝ)*X 1 0+(3456767/7812500 : ℝ)*X 1 1+(4424661329/10000000000 : ℝ)*X 1 2+(4156789043/10000000000 : ℝ)*X 2 0+(3456767/7812500 : ℝ)*X 2 1+(4424661329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1318_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62847/100000 : ℝ) ≤ (-4281254524814181889546798723693/6812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289573/100000000000000 : ℝ)*(lower0) + (9977619/100000000000000 : ℝ)*(lower3) + (3289751/50000000000000 : ℝ)*(lower4) + (1446859357393307/50000000000000 : ℝ)*(major0) + (1446859357393307/50000000000000 : ℝ)*(major1) + (1446859357393307/50000000000000 : ℝ)*(major2) + (503950933/100000000000000 : ℝ)*(sp1) + (1148810251/20000000000000 : ℝ)*(sp2) + (876845931/50000000000000 : ℝ)*(sp3) + (1963349770037423/50000000000000 : ℝ)*(sp4) + (1963352067488991/50000000000000 : ℝ)*(sp5) + (196334944743883/5000000000000 : ℝ)*(sp6) + (1881679071324621/100000000000000 : ℝ)*(sp7) + (1274713517/25000000000000 : ℝ)*(sp12) + (1881680825016483/100000000000000 : ℝ)*(f.failure) + (1963352319464457/50000000000000 : ℝ)*(f.sum) + (2482101795143/1635000000000000000000000000 : ℝ)*base65 + (2878572499146269/27250000000000000000000000000000 : ℝ)*base68 + (247927672634853731/27250000000000000000000000000000 : ℝ)*base69 + (285979310462603731/27250000000000000000000000000000 : ℝ)*base71 + (28031132812477/1635000000000000000000000000 : ℝ)*base74 + (174837880303353731/27250000000000000000000000000000 : ℝ)*base75 + (133451117073853731/27250000000000000000000000000000 : ℝ)*base77 + (59778198449853731/27250000000000000000000000000000 : ℝ)*base79 + (3243870396679/817500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (57992689/10000000000000000000000 : ℝ)*base90 + (57992689/10000000000000000000000 : ℝ)*base92 + (57992689/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11779/20000 : ℝ) ≤ (88272381983214525366404321844631/149875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8069977/12500000000000 : ℝ)*(upper0) + (30864939/50000000000000 : ℝ)*(lower1) + (224799673/100000000000000 : ℝ)*(upper4) + (1480802414653921/50000000000000 : ℝ)*(major0) + (1480802414653921/50000000000000 : ℝ)*(major1) + (1480802414653921/50000000000000 : ℝ)*(major2) + (1988875005173543/50000000000000 : ℝ)*(sp0) + (3977736909427749/100000000000000 : ℝ)*(sp1) + (19888677810133/500000000000 : ℝ)*(sp2) + (385164279625237/20000000000000 : ℝ)*(sp3) + (7794571139/50000000000000 : ℝ)*(sp5) + (4234135857/25000000000000 : ℝ)*(sp6) + (13266653/400000000000 : ℝ)*(sp7) + (2488222941/100000000000000 : ℝ)*(sp8) + (385164942957887/20000000000000 : ℝ)*(f.failure) + (994438124642507/25000000000000 : ℝ)*(f.sum) + (20459413480589/17985000000000000000000000000 : ℝ)*base65 + (154496809843903193/27250000000000000000000000000000 : ℝ)*base67 + (263113956499903193/27250000000000000000000000000000 : ℝ)*base69 + (253306673052403193/27250000000000000000000000000000 : ℝ)*base71 + (770966895203521/17985000000000000000000000000 : ℝ)*base74 + (22960232114596807/27250000000000000000000000000000 : ℝ)*base76 + (166623454151403193/27250000000000000000000000000000 : ℝ)*base77 + (1329950335233596807/27250000000000000000000000000000 : ℝ)*base80 + (12195100434821/4496250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2674021/2000000000000000000000 : ℝ)*base90 + (2674021/2000000000000000000000 : ℝ)*base92 + (2674021/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79813/100000 : ℝ) ≤ (4784928002192435536736237433/5995000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44996457/50000000000000 : ℝ)*(upper0) + (17646391/50000000000000 : ℝ)*(upper1) + (95408987/100000000000000 : ℝ)*(lower3) + (21159313/25000000000000 : ℝ)*(upper4) + (409335580366797/12500000000000 : ℝ)*(major0) + (409335580366797/12500000000000 : ℝ)*(major1) + (409335580366797/12500000000000 : ℝ)*(major2) + (117811084013/100000000000000 : ℝ)*(sp2) + (3340829121/6250000000000 : ℝ)*(sp3) + (279666917/2000000000000 : ℝ)*(sp4) + (549167622747273/12500000000000 : ℝ)*(sp8) + (878670993064807/20000000000000 : ℝ)*(sp9) + (2196618577120011/50000000000000 : ℝ)*(sp10) + (1064677881506519/50000000000000 : ℝ)*(sp11) + (1064704608139487/50000000000000 : ℝ)*(f.failure) + (878670993064807/20000000000000 : ℝ)*(f.sum) + (1126264816041/1498750000000000000000000000 : ℝ)*base65 + (55753402277175901/6812500000000000000000000000000 : ℝ)*base67 + (49326395323699099/6812500000000000000000000000000 : ℝ)*base70 + (9582072841113401/6812500000000000000000000000000 : ℝ)*base71 + (3172198370023/749375000000000000000000000 : ℝ)*base73 + (1599231516238401/6812500000000000000000000000000 : ℝ)*base75 + (18844638702636599/6812500000000000000000000000000 : ℝ)*base78 + (20475879422074099/6812500000000000000000000000000 : ℝ)*base80 + (1451011170683/187343750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (34666821/5000000000000000000000 : ℝ)*base90 + (34666821/5000000000000000000000 : ℝ)*base92 + (34666821/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42129/50000 : ℝ) ≤ (-11479796409548153464790644877169/13625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133484893/50000000000000 : ℝ)*(upper3) + (129423/781250000000 : ℝ)*(lower4) + (17316609/25000000000000 : ℝ)*(upper5) + (1655442166473777/50000000000000 : ℝ)*(major0) + (1655442166473777/50000000000000 : ℝ)*(major1) + (1655442166473777/50000000000000 : ℝ)*(major2) + (5223678741/100000000000000 : ℝ)*(sp4) + (25033026279/20000000000000 : ℝ)*(sp5) + (42416386323/25000000000000 : ℝ)*(sp6) + (9259801187/10000000000000 : ℝ)*(sp7) + (2248450001530393/50000000000000 : ℝ)*(sp12) + (1124195015402033/25000000000000 : ℝ)*(sp13) + (1124183890298559/25000000000000 : ℝ)*(sp14) + (538213992493599/25000000000000 : ℝ)*(sp15) + (2152948567986267/100000000000000 : ℝ)*(f.failure) + (562113153342441/12500000000000 : ℝ)*(f.sum) + (410964893897/68125000000000000000000000 : ℝ)*base65 + (217632131882225241/27250000000000000000000000000000 : ℝ)*base67 + (19969088020475241/27250000000000000000000000000000 : ℝ)*base69 + (526453557637725241/27250000000000000000000000000000 : ℝ)*base71 + (2387109096593/272500000000000000000000000 : ℝ)*base73 + (251202498326475241/27250000000000000000000000000000 : ℝ)*base75 + (191769411369975241/27250000000000000000000000000000 : ℝ)*base77 + (5941778285475241/27250000000000000000000000000000 : ℝ)*base79 + (172497961989/136250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (55785561/10000000000000000000000 : ℝ)*base90 + (55785561/10000000000000000000000 : ℝ)*base92 + (55785561/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1318_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11779/20000 : ℝ) else (79813/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42129/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1318_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1318_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11779/20000 : ℝ) else (79813/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42129/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1318_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4277/1024 : ℝ) ≤ p) (hpb : p ≤ (2139/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153783717/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11779/20000 : ℝ) else (79813/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42129/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1318_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
