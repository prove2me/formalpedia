-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff8.coarse_failure_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T15:39:58.913218+00:00
-- url     : https://prove2.me/submissions/f6cdc954-0070-4e8f-9ee0-763df1383e8e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_lp_0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_lp_1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_lp_2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_lp_3
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
/- Generic norm and normalization arguments retain the Apache-2.0 attribution
to Ezzeri Esa, bwdaugherty and Yuxuan Xu. The relative-coordinate LP and
cutoff-8 inequalities are checked explicitly below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
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
namespace HlawkaSchatten.DiagonalConstruction
variable {ι : Type*} [Fintype ι]
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring
end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalFailureBundle.Failure
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

/-- The envelope hypothesis at `q` confines the normalized total below `q`. -/
theorem normalized_failure_total_lt_q {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    lpNorm p (x + y + z) < q := by
  have hT1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp hK x y z hS hf
  by_contra hn
  have hle : q ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp.le
    (show q ∈ Set.Ico 0 1 from ⟨hq0.le, hq1⟩)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hT1⟩) hle
  linarith

end Deficit

/-- Scaled normalization: singleton norms sum to 3, each at most the total,
and the total is below `3q`. -/
theorem scaled_failure {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    ∃ x y z : Fin 3 → ℝ, hlawkaDeficit p K x y z < 0 ∧
      lpNorm p x + lpNorm p y + lpNorm p z = 3 ∧
      lpNorm p x ≤ lpNorm p (x + y + z) ∧
      lpNorm p y ≤ lpNorm p (x + y + z) ∧
      lpNorm p z ≤ lpNorm p (x + y + z) ∧
      lpNorm p (x + y + z) < 3 * q := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ := exists_normalized_failure hp0 hK x y z hf
  have hT := normalized_failure_total_lt_q hp hK hq0 hq1 henvelope x y z hS hf
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have hsum : (3 : ℝ) • x + (3 : ℝ) • y + (3 : ℝ) • z = (3 : ℝ) • (x + y + z) := by
    rw [smul_add, smul_add]
  refine ⟨(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp0, h3]
    linarith
  · rw [lpNorm_smul hp0, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, h3]
    linarith


end HlawkaSchatten.DiagonalFailureBundle.Failure
namespace HlawkaSchatten.DiagonalFailureBundle
theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _
theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e
theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]
end HlawkaSchatten.DiagonalFailureBundle
namespace HlawkaSchatten.DiagonalCutoff16
theorem upper_root_of_power {x y a : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ y^a) : x^(1/a) ≤ y := by
  have hh := Real.rpow_le_rpow hx h (one_div_nonneg.mpr ha.le)
  rw [← Real.rpow_mul hy, mul_one_div_cancel ha.ne', Real.rpow_one] at hh
  exact hh
end HlawkaSchatten.DiagonalCutoff16
namespace HlawkaSchatten.DiagonalCutoff16Scalar
theorem two_tail_norm_bound (m : ℕ) (hm : 1 ≤ m)
    {p S y1 y2 rho cap eps : ℝ}
    (hp : (m : ℝ) ≤ p) (hS : 0 ≤ S) (hScap : S ≤ cap) (hcap : 0 < cap)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hy1 : |y1| ≤ rho * S) (hy2 : |y2| ≤ rho * S)
    (hcert : 2 * rho ^ m * cap ≤ (m : ℝ) * eps) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  have hp0 : 0 < p := by linarith
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hzero : S = 0 := hS0.symm
    subst S
    have hy10 : y1 = 0 := abs_nonpos_iff.mp (by simpa using hy1)
    have hy20 : y2 = 0 := abs_nonpos_iff.mp (by simpa using hy2)
    subst y1 y2
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using heps
  · rw [abs_of_pos hSpos]
    have hpow : rho ^ p ≤ rho ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hrho hrho1 (by positivity) hp
    have hy (y : ℝ) (hy : |y| ≤ rho * S) :
        |y| ^ p ≤ rho ^ m * S ^ p := by
      calc
        _ ≤ (rho * S) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
        _ = rho ^ p * S ^ p := Real.mul_rpow hrho hSpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    have hnum : 2 * rho ^ m ≤ p * (eps / S) := by
      have h1 : 2 * rho ^ m ≤ (m : ℝ) * eps / cap := (le_div_iff₀ hcap).2 hcert
      have h2 : eps / cap ≤ eps / S := div_le_div_of_nonneg_left heps hSpos hScap
      have h3 := mul_le_mul hp h2 (div_nonneg heps hcap.le) (by positivity : (0 : ℝ) ≤ p)
      calc
        _ ≤ (m : ℝ) * eps / cap := h1
        _ = (m : ℝ) * (eps / cap) := by ring
        _ ≤ p * (eps / S) := h3
    have hbern : 1 + p * (eps / S) ≤ (1 + eps / S) ^ p :=
      one_add_mul_self_le_rpow_one_add (by have := div_nonneg heps hSpos.le; linarith) hp1
    have heq : (S + eps) ^ p = S ^ p * (1 + eps / S) ^ p := by
      rw [← Real.mul_rpow hSpos.le (by positivity)]
      congr 1
      field_simp
    have h1 := hy y1 hy1
    have h2 := hy y2 hy2
    have h3 := mul_le_mul_of_nonneg_right hnum (show 0 ≤ S ^ p by positivity)
    have h4 := mul_le_mul_of_nonneg_left hbern (show 0 ≤ S ^ p by positivity)
    have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + eps) ^ p := by
      rw [heq]
      nlinarith
    calc
      _ ≤ ((S + eps) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = S + eps := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']
end HlawkaSchatten.DiagonalCutoff16Scalar
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

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff8

/- Two pairwise sums attain their largest absolute coordinate at the same
   coordinate. Keep both triangle bounds for the third pair. The two possible
   relative signs give the same upper bound for the sum of all pair norms. -/
theorem collision_pair_sum_bound
    {a b c Na Nb Nc P1 P2 P3 S T d s r : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (hb : |b| ≤ Nb) (hc : |c| ≤ Nc)
    (hcol : |a+b+c| ≤ T) (ha : |a| ≤ Na)
    (h1 : d*P1 ≤ s*(a+b)) (h2 : d*P2 ≤ r*(a+c))
    (h3 : P3 ≤ Nb+Nc) (h3' : P3 ≤ T+Na)
    (hS : Na+Nb+Nc = S)
    (hmin : S-2*T ≤ Na) (hmax : Na ≤ T) :
    d*(P1+P2+P3) ≤ d*S+(2-d)*T := by
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have ha' := abs_le.mp ha
  have hcol' := abs_le.mp hcol
  have h3d := mul_le_mul_of_nonneg_left h3 hd
  have h3d' := mul_le_mul_of_nonneg_left h3' hd
  have hmind := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hd1)
  have hmaxd := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hd1)
  have hSd := congrArg (fun x : ℝ => d*x) hS
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> nlinarith

theorem collision_incompatible_with_failure
    {P T A d k : ℝ}
    (hd : 0 < d) (hk : 0 ≤ k)
    (hP : d*P ≤ 3*d+(2-d)*T)
    (hT : T ≤ A) (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*A < 3*d*(k-1))
    (hfail : k*(6-P)+T < 3) : False := by
  have hPk := mul_le_mul_of_nonneg_left hP hk
  have hTA := mul_le_mul_of_nonneg_left hT hslope
  have hfaild := mul_lt_mul_of_pos_left hfail hd
  nlinarith

/- These rational constants leave a margin greater than two in the normalized
   deficit. The separate scalar bounds k ≤ K_p and T ≤ A are not asserted here. -/
theorem collision_parameters8 :
    3*(87/100 : ℝ)^8 < 1 ∧
    0 ≤ (159/50 : ℝ)*(2-87/100)-87/100 ∧
    ((159/50 : ℝ)*(2-87/100)-87/100)*(57/40) <
      3*(87/100)*(159/50-1) := by
  norm_num

end HlawkaSchatten.DiagonalCutoff8

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff8
theorem norm_le_three_root_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem relative_coordinate8 {p : ℝ} (hp : 8 ≤ p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    (87/100 : ℝ) * lpNorm p x ≤ |x i| := by
  have hp0 : 0 < p := by linarith
  have hroot : (3 : ℝ)^(1/p) ≤ 100/87 := by
    calc
      _ ≤ (3 : ℝ)^(1/(8 : ℝ)) := Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (one_div_le_one_div_of_le (by norm_num) hp)
      _ ≤ 100/87 := HlawkaSchatten.DiagonalCutoff16.upper_root_of_power
        (by norm_num : (0 : ℝ) < 8) (by norm_num) (by norm_num)
        (by norm_num [Real.rpow_natCast])
  have h := norm_le_three_root_max hp0 x i hi
  have h' := mul_le_mul_of_nonneg_right hroot (abs_nonneg (x i))
  linarith

end HlawkaSchatten.DiagonalCutoff8
/- Coordinate permutation and normalization follow the Apache-2.0 proofs of
Ezzeri Esa, bwdaugherty and Yuxuan Xu. Relative main-coordinate bounds and the
combined-pair-gap contradiction are the new cutoff-12 improvements. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalFailureBundle

structure RelativeOrientedData (p q : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop where
  sum : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3
  norm_le_total : ∀ i, lpNorm p (X i) ≤ lpNorm p (X 0+X 1+X 2)
  total_one : 1 ≤ lpNorm p (X 0+X 1+X 2)
  total_cap : lpNorm p (X 0+X 1+X 2) < 3*q
  main0 : (87/100 : ℝ)*lpNorm p (X 1+X 2) ≤ X 1 0+X 2 0
  main1 : (87/100 : ℝ)*lpNorm p (X 0+X 2) ≤ X 0 1+X 2 1
  main2 : (87/100 : ℝ)*lpNorm p (X 0+X 1) ≤ X 0 2+X 1 2
  linear_failure : lpNorm p (X 0+X 1+X 2) - (159/50 : ℝ)*
    (lpNorm p (X 1+X 2)+lpNorm p (X 0+X 2)+lpNorm p (X 0+X 1)) ≤ 3-6*(159/50 : ℝ)
  failure : tripleDeficit p (cyclicConstant p) X < 0

theorem exists_relative_signed_coord {p : ℝ} (hp : 8 ≤ p) (v : Fin 3 → ℝ) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (87/100 : ℝ)*lpNorm p v ≤ s*v i := by
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |v i|) Finset.univ_nonempty
  have h := relative_coordinate8 hp v i (fun j => hi j (Finset.mem_univ _))
  by_cases hv : 0 ≤ v i
  · exact ⟨i,1,Or.inl rfl,by simpa [abs_of_nonneg hv] using h⟩
  · exact ⟨i,-1,Or.inr rfl,by simpa [abs_of_neg (lt_of_not_ge hv)] using h⟩

theorem exists_relative_oriented_failure {p q : ℝ} (hp : 8 ≤ p)
    (hq0 : 0 < q) (hqcap : q ≤ 19/40)
    (hlinear : (159/50 : ℝ) < cyclicConstant p)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, RelativeOrientedData p q X := by
  have hp1 : 1 < p := by linarith
  set K := cyclicConstant p with hKdef
  have hK : (159/50 : ℝ) < K := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT, hTq⟩ :=
    Failure.scaled_failure hp1 (by linarith) hq0
      (by linarith) henvelope x y z hf
  set T := lpNorm p (x+y+z) with hTdef
  have hT : T < 3*q := by linarith
  have hG0 := pairGapSum_nonneg hp1.le x y z
  have hKG : K*pairGapSum (lpNorm p) x y z < 3-T := by
    have h := hf
    rw [hlawkaDeficit_eq, tripleGap, hS] at h
    linarith
  have hG : (159/50 : ℝ)*pairGapSum (lpNorm p) x y z+T < 3 := by
    have := mul_le_mul_of_nonneg_right hK.le hG0
    linarith
  have hTone : 1 ≤ T := by linarith
  have hTglobal : T ≤ 57/40 := by linarith
  have hPfail : (159/50 : ℝ)*(6-(lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z)))+T < 3 := by
    dsimp only [pairGapSum,pairGap] at hG
    linarith
  have hyzT : lpNorm p (y+z) ≤ T+lpNorm p x := by
    have h := lpNorm_add hp1.le (x+y+z) (-x)
    have he : (x+y+z)+(-x) = y+z := by abel
    rw [he,lpNorm_neg] at h
    exact h
  have hxzT : lpNorm p (x+z) ≤ T+lpNorm p y := by
    have h := lpNorm_add hp1.le (x+y+z) (-y)
    have he : (x+y+z)+(-y) = x+z := by abel
    rw [he,lpNorm_neg] at h
    exact h
  have hxyT : lpNorm p (x+y) ≤ T+lpNorm p z := by
    have h := lpNorm_add hp1.le (x+y+z) (-z)
    have he : (x+y+z)+(-z) = x+y := by abel
    rw [he,lpNorm_neg] at h
    exact h
  obtain ⟨i,s,hs,hsxy⟩ := exists_relative_signed_coord hp (x+y)
  obtain ⟨j,r,hr,hrxz⟩ := exists_relative_signed_coord hp (x+z)
  obtain ⟨k,t,ht,htyz⟩ := exists_relative_signed_coord hp (y+z)
  simp only [Pi.add_apply, mul_add] at hsxy hrxz htyz
  have hxa (l : Fin 3) : |x l| ≤ lpNorm p x := norm_apply_le_lpNorm hp1.le x l
  have hya (l : Fin 3) : |y l| ≤ lpNorm p y := norm_apply_le_lpNorm hp1.le y l
  have hza (l : Fin 3) : |z l| ≤ lpNorm p z := norm_apply_le_lpNorm hp1.le z l
  have habs (l : Fin 3) : |x l+y l+z l| ≤ T := norm_apply_le_lpNorm hp1.le (x+y+z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    have hb := collision_pair_sum_bound (d := (87/100 : ℝ)) (S := (3 : ℝ))
      (P1 := lpNorm p (x+y)) (P2 := lpNorm p (x+z))
      (by norm_num) (by norm_num) hs hr (hya i) (hza i) (habs i) (hxa i)
      (by nlinarith only [hsxy]) (by nlinarith only [hrxz])
      (lpNorm_add hp1.le y z) hyzT hS (by linarith) hxT
    exact collision_incompatible_with_failure (k := (159/50 : ℝ))
      (d := (87/100 : ℝ)) (A := (57/40 : ℝ))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      (by norm_num) (by norm_num) (by nlinarith only [hb]) hTglobal
      (by norm_num) (by norm_num) hPfail

  have hik : i ≠ k := by
    intro heq
    subst k
    have hcol : |y i+x i+z i| ≤ T := by
      rw [show y i+x i+z i = x i+y i+z i by ring]; exact habs i
    have hb := collision_pair_sum_bound (d := (87/100 : ℝ)) (S := (3 : ℝ))
      (by norm_num) (by norm_num) hs ht (hxa i) (hza i) hcol (hya i)
      (P1 := lpNorm p (x+y)) (P2 := lpNorm p (y+z))
      (by nlinarith only [hsxy]) (by nlinarith only [htyz])
      (lpNorm_add hp1.le x z) hxzT (by linarith) (by linarith) hyT
    exact collision_incompatible_with_failure (k := (159/50 : ℝ))
      (d := (87/100 : ℝ)) (A := (57/40 : ℝ))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      (by norm_num) (by norm_num) (by nlinarith only [hb]) hTglobal
      (by norm_num) (by norm_num) hPfail

  have hjk : j ≠ k := by
    intro heq
    subst k
    have hcol : |z j+x j+y j| ≤ T := by
      rw [show z j+x j+y j = x j+y j+z j by ring]; exact habs j
    have hb := collision_pair_sum_bound (d := (87/100 : ℝ)) (S := (3 : ℝ))
      (by norm_num) (by norm_num) hr ht (hxa j) (hya j) hcol (hza j)
      (P1 := lpNorm p (x+z)) (P2 := lpNorm p (y+z))
      (by nlinarith only [hrxz]) (by nlinarith only [htyz])
      (lpNorm_add hp1.le x y) hxyT (by linarith) (by linarith) hzT
    exact collision_incompatible_with_failure (k := (159/50 : ℝ))
      (d := (87/100 : ℝ)) (A := (57/40 : ℝ))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      (by norm_num) (by norm_num) (by nlinarith only [hb]) hTglobal
      (by norm_num) (by norm_num) hPfail

  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = T := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have huv : lpNorm p (u + v) = lpNorm p (x + y) := by
    dsimp [u, v]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have huw : lpNorm p (u + w) = lpNorm p (x + z) := by
    dsimp [u, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hvw : lpNorm p (v + w) = lpNorm p (y + z) := by
    dsimp [v, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hpgs : pairGapSum (lpNorm p) u v w = pairGapSum (lpNorm p) x y z := by
    simp only [pairGapSum, pairGap, hu, hv, hw, huv, huw, hvw]
  have e0 : v 0 + w 0 = t * y k + t * z k := by simp [v, w, orient, e, f, signs]
  have e1 : u 1 + w 1 = r * x j + r * z j := by simp [u, w, orient, e, f, signs]
  have e2 : u 2 + v 2 = s * x i + s * y i := by simp [u, v, orient, e, f, signs]
  let X : Fin 3 → Fin 3 → ℝ := ![u, v, w]
  have hNX : ∀ l, lpNorm p (X l) ≤ T := by
    intro l
    fin_cases l
    · change lpNorm p u ≤ T
      rw [hu]; exact hxT
    · change lpNorm p v ≤ T
      rw [hv]; exact hyT
    · change lpNorm p w ≤ T
      rw [hw]; exact hzT
  have hlin : T - (159/50 : ℝ) * (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) ≤
      3 - 6 * (159/50 : ℝ) := by
    have hgf : pairGapSum (lpNorm p) u v w =
        6 - (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) := by
      dsimp only [pairGapSum, pairGap]
      rw [hu, hv, hw]
      linarith
    rw [← hpgs, hgf] at hG
    linarith
  refine ⟨![u, v, w], ?_⟩
  constructor
  · change lpNorm p u + lpNorm p v + lpNorm p w = 3
    rw [hu, hv, hw]; exact hS
  · intro l
    change lpNorm p (X l) ≤ lpNorm p (u + v + w)
    rw [hsumNorm]
    exact hNX l
  · change 1 ≤ lpNorm p (u + v + w)
    rw [hsumNorm]; exact hTone
  · change lpNorm p (u + v + w) < 3*q
    rw [hsumNorm]; exact hT
  · change (87/100 : ℝ)*lpNorm p (v+w) ≤ v 0+w 0
    rw [hvw, e0]; linarith
  · change (87/100 : ℝ)*lpNorm p (u+w) ≤ u 1+w 1
    rw [huw, e1]; linarith
  · change (87/100 : ℝ)*lpNorm p (u+v) ≤ u 2+v 2
    rw [huv, e2]; linarith
  · change lpNorm p (u+v+w) - (159/50 : ℝ) * (lpNorm p (v+w)+lpNorm p (u+w)+lpNorm p (u+v)) ≤ _
    rw [hsumNorm]; exact hlin
  · change hlawkaDeficit p K u v w < 0
    dsimp [u, v, w]
    rwa [hlawkaDeficit_orient p K e signs x y z hsigns]

end HlawkaSchatten.DiagonalCutoff8

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
namespace HlawkaSchatten.DiagonalCutoff8









theorem relative_coarse_tail_oriented (p : ℝ) (hp : 8 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (N P : Fin 3 → ℝ) (T : ℝ)
    (hNdef : ∀ i, N i = lpNorm p (X i))
    (hP0 : P 0 = lpNorm p (X 1+X 2))
    (hP1 : P 1 = lpNorm p (X 0+X 2))
    (hP2 : P 2 = lpNorm p (X 0+X 1))
    (hTdef : T = lpNorm p (X 0+X 1+X 2))
    (hS : N 0+N 1+N 2 = 3) (hNT : ∀ i, N i ≤ T)
    (hT1 : 1 ≤ T) (hTcap : T ≤ 57/40)
    (hmain0 : (87/100 : ℝ)*P 0 ≤ X 1 0+X 2 0)
    (hmain1 : (87/100 : ℝ)*P 1 ≤ X 0 1+X 2 1)
    (hmain2 : (87/100 : ℝ)*P 2 ≤ X 0 2+X 1 2)
    (hfail : T-(159/50 : ℝ)*(P 0+P 1+P 2) ≤ 3-6*(159/50 : ℝ)) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j+X k) ≤ X j i+X k i+1/200 := by

  have hp1 : 1 ≤ p := by linarith
  have hpn : 0 < p := by linarith
  have hp12 : 8 ≤ p := by linarith
  have hnpos (i : Fin 3) : 0 ≤ N i := by rw [hNdef]; exact lpNorm_nonneg p (X i)
  have hcoord (j i : Fin 3) : -N j ≤ X j i ∧ X j i ≤ N j := by
    have hc := norm_apply_le_lpNorm hp1 (X j) i
    rw [Real.norm_eq_abs, ← hNdef] at hc
    exact abs_le.mp hc
  have hn0 := hnpos 0
  rcases hcoord 0 0 with ⟨hx00l, hx00u⟩
  rcases hcoord 0 1 with ⟨hx01l, hx01u⟩
  rcases hcoord 0 2 with ⟨hx02l, hx02u⟩
  have hn1 := hnpos 1
  rcases hcoord 1 0 with ⟨hx10l, hx10u⟩
  rcases hcoord 1 1 with ⟨hx11l, hx11u⟩
  rcases hcoord 1 2 with ⟨hx12l, hx12u⟩
  have hn2 := hnpos 2
  rcases hcoord 2 0 with ⟨hx20l, hx20u⟩
  rcases hcoord 2 1 with ⟨hx21l, hx21u⟩
  rcases hcoord 2 2 with ⟨hx22l, hx22u⟩
  have hnt0 := hNT 0
  have ht0 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 0
  rw [Real.norm_eq_abs, ← hTdef] at ht0
  simp only [Pi.add_apply] at ht0
  rcases abs_le.mp ht0 with ⟨ht0l, ht0u⟩
  have hnt1 := hNT 1
  have ht1 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 1
  rw [Real.norm_eq_abs, ← hTdef] at ht1
  simp only [Pi.add_apply] at ht1
  rcases abs_le.mp ht1 with ⟨ht1l, ht1u⟩
  have hnt2 := hNT 2
  have ht2 := norm_apply_le_lpNorm hp1 (X 0 + X 1 + X 2) 2
  rw [Real.norm_eq_abs, ← hTdef] at ht2
  simp only [Pi.add_apply] at ht2
  rcases abs_le.mp ht2 with ⟨ht2l, ht2u⟩
  have hp0n : 0 ≤ P 0 := by rw [hP0]; exact lpNorm_nonneg p _
  have hp0u : P 0 ≤ N 1 + N 2 := by rw [hP0, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp1n : 0 ≤ P 1 := by rw [hP1]; exact lpNorm_nonneg p _
  have hp1u : P 1 ≤ N 0 + N 2 := by rw [hP1, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  have hp2n : 0 ≤ P 2 := by rw [hP2]; exact lpNorm_nonneg p _
  have hp2u : P 2 ≤ N 0 + N 1 := by rw [hP2, hNdef, hNdef]; exact lpNorm_add hp1 _ _
  let v : Fin 16 → ℝ := fun z ↦ match z.val with
    | 0 => X 0 0
    | 1 => X 0 1
    | 2 => X 0 2
    | 3 => X 1 0
    | 4 => X 1 1
    | 5 => X 1 2
    | 6 => X 2 0
    | 7 => X 2 1
    | 8 => X 2 2
    | 9 => N 0
    | 10 => N 1
    | 11 => N 2
    | 12 => P 0
    | 13 => P 1
    | 14 => P 2
    | 15 => T
    | _ => 0


  have h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn0]

  have h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt0]

  have h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn1]

  have h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt1]

  have h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hn2]

  have h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hnt2]

  have h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ) := by norm_num [v]; linarith only [hT1]

  have h7 : ((1 : ℝ) * v 15) ≤ (57/40 : ℝ) := by norm_num [v]; linarith only [hTcap]

  have h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00l]

  have h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx00u]

  have h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01l]

  have h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx01u]

  have h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02l]

  have h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx02u]

  have h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10l]

  have h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx10u]

  have h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11l]

  have h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx11u]

  have h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12l]

  have h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx12u]

  have h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20l]

  have h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx20u]

  have h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21l]

  have h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx21u]

  have h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22l]

  have h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hx22u]

  have h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0l]

  have h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht0u]

  have h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0n]

  have h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp0u]

  have h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (87/100 : ℝ) * v 12) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hmain0]

  have h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1l]

  have h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht1u]

  have h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1n]

  have h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp1u]

  have h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (87/100 : ℝ) * v 13) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hmain1]

  have h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2l]

  have h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ) := by norm_num [v]; linarith only [ht2u]

  have h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2n]

  have h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hp2u]

  have h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (87/100 : ℝ) * v 14) ≤ (0 : ℝ) := by norm_num [v]; linarith only [hmain2]

  have h41 : ((-159/50 : ℝ) * v 12 + (-159/50 : ℝ) * v 13 + (-159/50 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-402/25 : ℝ) := by norm_num [v]; linarith only [hfail]

  have heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = 3 := by norm_num [v];linarith only [hS]

  have step0 := coarse_lp_0 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 heq

  norm_num [v] at step0
  rcases step0 with ⟨a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8, a0_9, a0_10, a0_11, a0_12, a0_13, a0_14⟩

  have tail0_0 : P 0 ≤ X 1 0+X 2 0+(1927100749045261430403/15625000000000000000000 : ℝ) := by
    clear * - hp hP0 hx10u hx20u hS hn0 a0_0 a0_1 a0_2 a0_3 a0_4
    rw [hP0,lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a0_0])
      (by linarith only [hx10u,hx20u,hS,hn0]) (by norm_num)
      (show (0 : ℝ) ≤ (399/500 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a0_2],by linarith only [a0_1]⟩
    · exact abs_le.mpr ⟨by linarith only [a0_4],by linarith only [a0_3]⟩
    · norm_num

  have tail0_1 : P 1 ≤ X 0 1+X 2 1+(1927100749045261430403/15625000000000000000000 : ℝ) := by
    clear * - hp hP1 hx01u hx21u hS hn1 a0_5 a0_6 a0_7 a0_8 a0_9
    rw [hP1,lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a0_5])
      (by linarith only [hx01u,hx21u,hS,hn1]) (by norm_num)
      (show (0 : ℝ) ≤ (399/500 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a0_7],by linarith only [a0_6]⟩
    · exact abs_le.mpr ⟨by linarith only [a0_9],by linarith only [a0_8]⟩
    · norm_num

  have tail0_2 : P 2 ≤ X 0 2+X 1 2+(1927100749045261430403/15625000000000000000000 : ℝ) := by
    clear * - hp hP2 hx02u hx12u hS hn2 a0_10 a0_11 a0_12 a0_13 a0_14
    rw [hP2,lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a0_10])
      (by linarith only [hx02u,hx12u,hS,hn2]) (by norm_num)
      (show (0 : ℝ) ≤ (399/500 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a0_12],by linarith only [a0_11]⟩
    · exact abs_le.mpr ⟨by linarith only [a0_14],by linarith only [a0_13]⟩
    · norm_num

  have h42 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1927100749045261430403/15625000000000000000000 : ℝ) := by norm_num [v];linarith only [tail0_0]

  have h43 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1927100749045261430403/15625000000000000000000 : ℝ) := by norm_num [v];linarith only [tail0_1]

  have h44 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1927100749045261430403/15625000000000000000000 : ℝ) := by norm_num [v];linarith only [tail0_2]

  have step1 := coarse_lp_1 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 heq

  norm_num [v] at step1
  rcases step1 with ⟨a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9, a1_10, a1_11, a1_12, a1_13, a1_14⟩

  have tail1_0 : P 0 ≤ X 1 0+X 2 0+(96776333278164985005603/4000000000000000000000000 : ℝ) := by
    clear * - hp hP0 hx10u hx20u hS hn0 a1_0 a1_1 a1_2 a1_3 a1_4
    rw [hP0,lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a1_0])
      (by linarith only [hx10u,hx20u,hS,hn0]) (by norm_num)
      (show (0 : ℝ) ≤ (651/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a1_2],by linarith only [a1_1]⟩
    · exact abs_le.mpr ⟨by linarith only [a1_4],by linarith only [a1_3]⟩
    · norm_num

  have tail1_1 : P 1 ≤ X 0 1+X 2 1+(96776333278164985005603/4000000000000000000000000 : ℝ) := by
    clear * - hp hP1 hx01u hx21u hS hn1 a1_5 a1_6 a1_7 a1_8 a1_9
    rw [hP1,lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a1_5])
      (by linarith only [hx01u,hx21u,hS,hn1]) (by norm_num)
      (show (0 : ℝ) ≤ (651/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a1_7],by linarith only [a1_6]⟩
    · exact abs_le.mpr ⟨by linarith only [a1_9],by linarith only [a1_8]⟩
    · norm_num

  have tail1_2 : P 2 ≤ X 0 2+X 1 2+(96776333278164985005603/4000000000000000000000000 : ℝ) := by
    clear * - hp hP2 hx02u hx12u hS hn2 a1_10 a1_11 a1_12 a1_13 a1_14
    rw [hP2,lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a1_10])
      (by linarith only [hx02u,hx12u,hS,hn2]) (by norm_num)
      (show (0 : ℝ) ≤ (651/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a1_12],by linarith only [a1_11]⟩
    · exact abs_le.mpr ⟨by linarith only [a1_14],by linarith only [a1_13]⟩
    · norm_num

  have h45 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (96776333278164985005603/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail1_0]

  have h46 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (96776333278164985005603/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail1_1]

  have h47 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (96776333278164985005603/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail1_2]

  have step2 := coarse_lp_2 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 heq

  norm_num [v] at step2
  rcases step2 with ⟨a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9, a2_10, a2_11, a2_12, a2_13, a2_14⟩

  have tail2_0 : P 0 ≤ X 1 0+X 2 0+(21371321427751088929443/4000000000000000000000000 : ℝ) := by
    clear * - hp hP0 hx10u hx20u hS hn0 a2_0 a2_1 a2_2 a2_3 a2_4
    rw [hP0,lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a2_0])
      (by linarith only [hx10u,hx20u,hS,hn0]) (by norm_num)
      (show (0 : ℝ) ≤ (539/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a2_2],by linarith only [a2_1]⟩
    · exact abs_le.mpr ⟨by linarith only [a2_4],by linarith only [a2_3]⟩
    · norm_num

  have tail2_1 : P 1 ≤ X 0 1+X 2 1+(21371321427751088929443/4000000000000000000000000 : ℝ) := by
    clear * - hp hP1 hx01u hx21u hS hn1 a2_5 a2_6 a2_7 a2_8 a2_9
    rw [hP1,lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a2_5])
      (by linarith only [hx01u,hx21u,hS,hn1]) (by norm_num)
      (show (0 : ℝ) ≤ (539/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a2_7],by linarith only [a2_6]⟩
    · exact abs_le.mpr ⟨by linarith only [a2_9],by linarith only [a2_8]⟩
    · norm_num

  have tail2_2 : P 2 ≤ X 0 2+X 1 2+(21371321427751088929443/4000000000000000000000000 : ℝ) := by
    clear * - hp hP2 hx02u hx12u hS hn2 a2_10 a2_11 a2_12 a2_13 a2_14
    rw [hP2,lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a2_10])
      (by linarith only [hx02u,hx12u,hS,hn2]) (by norm_num)
      (show (0 : ℝ) ≤ (539/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a2_12],by linarith only [a2_11]⟩
    · exact abs_le.mpr ⟨by linarith only [a2_14],by linarith only [a2_13]⟩
    · norm_num

  have h48 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (21371321427751088929443/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail2_0]

  have h49 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (21371321427751088929443/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail2_1]

  have h50 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (21371321427751088929443/4000000000000000000000000 : ℝ) := by norm_num [v];linarith only [tail2_2]

  have step3 := coarse_lp_3 v h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 heq

  norm_num [v] at step3
  rcases step3 with ⟨a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9, a3_10, a3_11, a3_12, a3_13, a3_14⟩

  have tail3_0 : P 0 ≤ X 1 0+X 2 0+(1/200 : ℝ) := by
    clear * - hp hP0 hx10u hx20u hS hn0 a3_0 a3_1 a3_2 a3_3 a3_4
    rw [hP0,lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a3_0])
      (by linarith only [hx10u,hx20u,hS,hn0]) (by norm_num)
      (show (0 : ℝ) ≤ (519/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a3_2],by linarith only [a3_1]⟩
    · exact abs_le.mpr ⟨by linarith only [a3_4],by linarith only [a3_3]⟩
    · norm_num

  have tail3_1 : P 1 ≤ X 0 1+X 2 1+(1/200 : ℝ) := by
    clear * - hp hP1 hx01u hx21u hS hn1 a3_5 a3_6 a3_7 a3_8 a3_9
    rw [hP1,lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a3_5])
      (by linarith only [hx01u,hx21u,hS,hn1]) (by norm_num)
      (show (0 : ℝ) ≤ (519/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a3_7],by linarith only [a3_6]⟩
    · exact abs_le.mpr ⟨by linarith only [a3_9],by linarith only [a3_8]⟩
    · norm_num

  have tail3_2 : P 2 ≤ X 0 2+X 1 2+(1/200 : ℝ) := by
    clear * - hp hP2 hx02u hx12u hS hn2 a3_10 a3_11 a3_12 a3_13 a3_14
    rw [hP2,lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [Pi.add_apply]
    apply two_tail_norm_bound (cap := (3 : ℝ)) 8 (by norm_num) hp
      (by linarith only [a3_10])
      (by linarith only [hx02u,hx12u,hS,hn2]) (by norm_num)
      (show (0 : ℝ) ≤ (519/1000 : ℝ) by norm_num) (by norm_num) (by norm_num)
    · exact abs_le.mpr ⟨by linarith only [a3_12],by linarith only [a3_11]⟩
    · exact abs_le.mpr ⟨by linarith only [a3_14],by linarith only [a3_13]⟩
    · norm_num

  rw [hP0] at tail3_0
  rw [hP1] at tail3_1
  rw [hP2] at tail3_2

  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction

  · change lpNorm p (X 1+X 2) ≤ X 1 0+X 2 0+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_0

  · change lpNorm p (X 2+X 1) ≤ X 2 0+X 1 0+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_0

  · change lpNorm p (X 0+X 2) ≤ X 0 1+X 2 1+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_1

  · change lpNorm p (X 2+X 0) ≤ X 2 1+X 0 1+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_1

  · change lpNorm p (X 0+X 1) ≤ X 0 2+X 1 2+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_2

  · change lpNorm p (X 1+X 0) ≤ X 1 2+X 0 2+1/200
    simpa only [add_comm,add_left_comm,add_assoc] using tail3_2


theorem relative_coarse_tail (p q : ℝ) (hp : 8 ≤ p) (hq : q ≤ 19/40)
    (X : Fin 3 → Fin 3 → ℝ) (d : RelativeOrientedData p q X) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j+X k) ≤ X j i+X k i+1/200 := by
  exact relative_coarse_tail_oriented p hp X (fun i => lpNorm p (X i))
    ![lpNorm p (X 1+X 2),lpNorm p (X 0+X 2),lpNorm p (X 0+X 1)]
    (lpNorm p (X 0+X 1+X 2)) (fun _ => rfl) rfl rfl rfl rfl
    d.sum d.norm_le_total d.total_one (by have h := d.total_cap; linarith)
    d.main0 d.main1 d.main2 d.linear_failure

theorem coarse_failure_reduction {p q : ℝ} (hp : 8 ≤ p)
    (hq0 : 0 < q) (hqcap : q ≤ 19/40)
    (hlinear : (159/50 : ℝ) < cyclicConstant p)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3 ∧
      1 ≤ lpNorm p (X 0+X 1+X 2) ∧
      lpNorm p (X 0+X 1+X 2) ≤ 3*q ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j+X k) ≤ X j i+X k i+1/200) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  obtain ⟨X,d⟩ := exists_relative_oriented_failure hp hq0 hqcap hlinear henvelope x y z hf
  exact ⟨X,d.sum,d.total_one,d.total_cap.le,relative_coarse_tail p q hp hqcap X d,d.failure⟩

end HlawkaSchatten.DiagonalCutoff8

theorem solution {p q : ℝ} (hp : 8 ≤ p)
    (hq0 : 0 < q) (hqcap : q ≤ 19/40)
    (hlinear : (159/50 : ℝ) < cyclicConstant p)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3 ∧
      1 ≤ lpNorm p (X 0+X 1+X 2) ∧
      lpNorm p (X 0+X 1+X 2) ≤ 3*q ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j+X k) ≤ X j i+X k i+1/200) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  exact HlawkaSchatten.DiagonalCutoff8.coarse_failure_reduction hp hq0 hqcap hlinear henvelope x y z hf

#print axioms solution
