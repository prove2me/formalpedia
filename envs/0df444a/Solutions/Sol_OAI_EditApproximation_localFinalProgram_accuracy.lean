-- Prove2me | solution 1 for OAI.EditApproximation.localFinalProgram_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:03.619639+00:00
-- url     : https://prove2.me/submissions/1e180b82-5a11-4497-be3d-b94c95bfeb3b

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedSeedPassCount_le_height
import Theorems.Thm_OAI_EditApproximation_localFinalProgramValue_eq
import Theorems.Thm_OAI_EditApproximation_localScheduledSeedNext_event
import Theorems.Thm_OAI_EditApproximation_physicalMedianUpdate_lower
import Theorems.Thm_OAI_EditApproximation_physicalProgram_expected_root_excess
import Theorems.Thm_OAI_EditApproximation_physicalProgram_expected_state_excess
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_stage_bounds
import Theorems.Thm_OAI_EditApproximation_physicalRefinement_zero_cost

section
-- module Solutions.OAIQ361V3_EA.Compat
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Accuracy
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRange_neZero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Accuracy assembly for the edit-distance approximation scheme

The probability and integer-conversion bounds of Section 8 of
*An Almost-Linear Approximation Scheme for Edit Distance*
(OpenAI, September 24, 2026) follow from the refinement estimate and
simultaneous seed guarantee using Markov's inequality.
-/

namespace EditApproximation

open MeasureTheory

/-- Clamping and rounding down preserve a one-sided approximation of an
integer distance.  This does not assert that an estimator has that bound. -/
theorem integerAnswer_spec {N D : ℕ} {value ε : ℝ}
    (hDN : D ≤ N) (hε : 0 ≤ ε)
    (hlower : (D : ℝ) ≤ value) (hupper : value ≤ (1 + ε) * D) :
    D ≤ integerAnswer N value ∧
      (integerAnswer N value : ℝ) ≤ (1 + ε) * D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hmin : (D : ℝ) ≤ min (N : ℝ) value :=
    le_min (by exact_mod_cast hDN) hlower
  have hnonneg : 0 ≤ max 0 (min (N : ℝ) value) := le_max_left _ _
  constructor
  · exact (Nat.le_floor_iff hnonneg).2 (hmin.trans (le_max_right _ _))
  · apply (Nat.floor_le hnonneg).trans
    exact max_le (by positivity) ((min_le_right _ _).trans hupper)

theorem goodExcess_nonneg {Ω : Type*} (G : Set Ω) (value : Ω → ℝ) (D : ℕ)
    (ω : Ω) : 0 ≤ goodExcess G value D ω := by
  classical
  by_cases hω : ω ∈ G <;> simp [goodExcess, hω]

/-- Markov's inequality converts the positive-excess expectation bound of
Section 8 into an approximation tail bound. -/
theorem goodExcess_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {G : Set Ω} {value : Ω → ℝ} {D : ℕ} {ℓ ε : ℝ}
    (hD : 0 < D) (hℓ : 0 < ℓ) (hε : 0 < ε)
    (hint : Integrable (goodExcess G value D) μ)
    (hmoment : (∫ ω, goodExcess G value D ω ∂μ) ≤ (D : ℝ) / ℓ) :
    μ.real {ω | ε * D ≤ goodExcess G value D ω} ≤ 1 / (ℓ * ε) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (goodExcess_nonneg G value D)) hint (ε * D)
  have htail : μ.real {ω | ε * D ≤ goodExcess G value D ω} ≤
      ((D : ℝ) / ℓ) / (ε * D) :=
    (le_div_iff₀ (mul_pos hε hDr)).2 (by
      simpa only [mul_comm] using hmarkov.trans hmoment)
  have hratio : ((D : ℝ) / ℓ) / (ε * D) = 1 / (ℓ * ε) := by
    field_simp
  rwa [hratio] at htail

/-- Final probability assembly, with the two genuinely unresolved
algorithmic guarantees exposed: a good-seed event and its excess moment.
The stronger success probability `4/5` implies the paper's `2/3`. -/
theorem final_answer_accuracy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Set Ω} {value : Ω → ℝ} {N D : ℕ} {ℓ ε : ℝ}
    (hvalue : Measurable value) (hDN : D ≤ N) (hD : 0 < D)
    (hℓ : 0 < ℓ) (hε : 0 < ε) (haccuracy : 10 ≤ ℓ * ε)
    (hseed : μ.real Gᶜ ≤ 1 / 10)
    (hlower : ∀ ω ∈ G, (D : ℝ) ≤ value ω)
    (hint : Integrable (goodExcess G value D) μ)
    (hmoment : (∫ ω, goodExcess G value D ω ∂μ) ≤ (D : ℝ) / ℓ) :
    (4 / 5 : ℝ) ≤ μ.real {ω | D ≤ integerAnswer N (value ω) ∧
      (integerAnswer N (value ω) : ℝ) ≤ (1 + ε) * D} := by
  classical
  let S : Set Ω := {ω | (D : ℝ) ≤ value ω ∧ value ω ≤ (1 + ε) * D}
  let B : Set Ω := {ω | ε * D ≤ goodExcess G value D ω}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const hvalue).inter
      (measurableSet_le hvalue measurable_const)
  have hbad : Sᶜ ⊆ Gᶜ ∪ B := by
    intro ω hω
    by_cases hG : ω ∈ G
    · right
      have hupper : (1 + ε) * D < value ω := by
        by_contra hn
        exact hω ⟨hlower ω hG, le_of_not_gt hn⟩
      change ε * D ≤ goodExcess G value D ω
      simp only [goodExcess, Set.indicator_of_mem hG]
      apply le_trans _ (le_max_left _ _)
      nlinarith
    · exact Or.inl hG
  have htail : μ.real B ≤ 1 / (ℓ * ε) :=
    goodExcess_tail μ hD hℓ hε hint hmoment
  have hratio : 1 / (ℓ * ε) ≤ (1 / 10 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) haccuracy
  have hfail : μ.real Sᶜ ≤ (1 / 5 : ℝ) := calc
    μ.real Sᶜ ≤ μ.real (Gᶜ ∪ B) := measureReal_mono hbad
    _ ≤ μ.real Gᶜ + μ.real B := measureReal_union_le (μ := μ) _ _
    _ ≤ 1 / 5 := by linarith
  have hmass : μ.real S + μ.real Sᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hS
  have hsuccess : (4 / 5 : ℝ) ≤ μ.real S := by linarith
  apply hsuccess.trans
  exact measureReal_mono (μ := μ) (fun ω hω =>
    integerAnswer_spec hDN hε.le hω.1 hω.2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Script

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

end Script



theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.treeLayerCodeWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem treeLayer_card (M d : ℕ) : Fintype.card (TreeLayer M d) = M ^ d := by
  induction d with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_punit
  | succ d ih =>
    change Fintype.card (TreeLayer M d × Fin M) = M ^ (d + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

theorem complete_tree_node_count (M J : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d)) ≤ 2 * M ^ J := by
  simp_rw [treeLayer_card]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, pow_succ]
    have hmul := Nat.mul_le_mul_right (M ^ J) hM
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem intervalTreeDepth_power_le (M nx : ℕ) (hM : 2 ≤ M) :
    M ^ intervalTreeDepth M nx ≤ M * max 1 nx := by
  by_cases hx : max 1 nx = 1
  · have hz : Nat.clog M 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Nat.clog_le_iff_le_pow hM).2 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [intervalTreeDepth, hx, hz, pow_zero, mul_one] using
      (by omega : 1 ≤ M)
  · have hx1 : 1 < max 1 nx := by omega
    have hdepth := Nat.clog_pos hM hx1
    have hpred := Nat.pow_pred_clog_lt_self hM hx1
    unfold intervalTreeDepth
    rw [← Nat.succ_pred_eq_of_pos hdepth,
      pow_succ]
    nlinarith

theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem intervalTreeDepth_node_count (M nx : ℕ) (hM : 2 ≤ M) :
    (∑ d ∈ range (intervalTreeDepth M nx + 1), Fintype.card (TreeLayer M d)) ≤
      2 * M * max 1 nx := by
  have hnodes := complete_tree_node_count M (intervalTreeDepth M nx) hM
  have hcapacity := intervalTreeDepth_power_le M nx hM
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DomainCounts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting the actual labeled state domain

The count includes repeated interval labels at different physical nodes.
It bounds simultaneous seed/amplification events without identifying those
nodes or replacing the finite target-state loops by an oracle.
-/

namespace EditApproximation

open Finset

theorem targetStates_length_le (n : ℕ) : (targetStates n).length ≤ (n + 1) ^ 2 := by
  unfold targetStates
  have h := list_flatMap_length_le (List.range (n + 1))
    (fun lo => (List.range (n + 1)).filterMap fun hi => makeTargetState n lo hi)
    (n + 1) (by
      intro lo hlo
      simpa only [List.length_range] using
        List.length_filterMap_le (fun hi => makeTargetState n lo hi) (List.range (n + 1)))
  simpa only [List.length_range, pow_two] using h

theorem labeledStateCount_le (M nx ny : ℕ) (hM : 2 ≤ M) :
    labeledStateCount M nx ny ≤ 2 * M * max 1 nx * (ny + 1) ^ 2 := by
  exact Nat.mul_le_mul (intervalTreeDepth_node_count M nx hM) (targetStates_length_le ny)

theorem computed_labeledStateCount_le (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    labeledStateCount (integerParameters N).M nx ny ≤ 2 ^ (5 * inputHeight N) := by
  have hbranch := computed_branching_bounds N hN hell
  have hM : (integerParameters N).M ≤ 2 ^ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hbranch.2.2
  have hx : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hy : ny + 1 ≤ 2 ^ inputHeight N :=
    (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  have hproduct : 2 * (integerParameters N).M * max 1 nx * (ny + 1) ^ 2 ≤
      2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 := by
    gcongr
  have hidentity : 2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 =
      2 ^ (4 * inputHeight N + 1) := by
    rw [← pow_mul]
    conv_lhs => lhs; lhs; lhs; change 2 ^ 1
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  exact (labeledStateCount_le _ _ _ hbranch.1).trans
    (hproduct.trans (hidentity.le.trans
      (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DomainExponential
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exponential form of the actual domain bound used in amplification. -/

namespace EditApproximation

theorem computed_labeledStateCount_exp (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    (labeledStateCount (integerParameters N).M nx ny : ℝ) ≤
      Real.exp (10 * inputHeight N) := by
  have hcount : (labeledStateCount (integerParameters N).M nx ny : ℝ) ≤
      (2 : ℝ) ^ (5 * inputHeight N) := by
    exact_mod_cast computed_labeledStateCount_le N nx ny hN hnx hny hell
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo (5 * inputHeight N)
  rw [← Real.exp_nat_mul, mul_one] at hpower
  apply hcount.trans (hpower.trans (Real.exp_le_exp.mpr ?_))
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [show (0 : ℝ) ≤ inputHeight N from Nat.cast_nonneg _]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteKeyRestriction
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting independent finite key streams preserves their exact
product law. Unused keys need not be allocated by a lazy implementation. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_restrict_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key) :
    (Measure.pi mu).map (fun draw k => draw (key k)) =
      Measure.pi (fun k => mu (key k)) := by
  have hindependent : iIndepFun (fun i (draw : ∀ j, X j) => draw i) (Measure.pi mu) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hrestricted := hindependent.precomp hinjective
  have hmap := hrestricted.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (key k)).aemeasurable)
  simpa only [(measurePreserving_eval mu _).map_eq] using hmap

theorem finite_pi_restrict_image_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : κ → Type*} [∀ k, MeasurableSpace (Y k)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key)
    (image : ∀ k, X (key k) → Y k) (himage : ∀ k, Measurable (image k)) :
    (Measure.pi mu).map (fun draw k => image k (draw (key k))) =
      Measure.pi (fun k => (mu (key k)).map (image k)) := by
  have hrestrict := finite_pi_restrict_map mu key hinjective
  have hproject : Measurable (fun draw : ∀ i, X i => fun k => draw (key k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (key k))
  have htransform : Measurable (fun draw : ∀ k, X (key k) => fun k => image k (draw k)) :=
    Measurable.of_eval (fun k => (himage k).comp (measurable_pi_apply k))
  refine (Measure.map_map htransform hproject).symm.trans ?_
  rw [hrestrict]
  exact Measure.pi_map_pi (fun k => (himage k).aemeasurable)

theorem finite_uniform_array_cast (R n m : ℕ) [NeZero n] [NeZero m] (h : n = m) :
    (Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin n)).toMeasure)).map
      (fun draw t => Fin.cast h (draw t)) =
    Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin m)).toMeasure) := by
  subst m
  simp only [Fin.cast_refl, id_eq, Measure.map_id']

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_StateDomain
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite labeled state type

Physical nodes are retained as depth/path pairs. In particular, repeated
empty intervals remain distinct entries of the seed and refinement tables.
-/

namespace EditApproximation

open Finset





theorem targetInterval_card_le (n : ℕ) :
    Fintype.card (TargetInterval n) ≤ (targetStates n).length := by
  exact (targetStates n).toFinset_card_le





theorem physicalNode_card (M J : ℕ) :
    Fintype.card (PhysicalNode M J) =
      ∑ d ∈ range (J + 1), Fintype.card (TreeLayer M d) := by
  rw [Fintype.card_sigma]
  rw [sum_fin_eq_sum_range]
  apply sum_congr rfl
  intro d hd
  rw [dite_eq_left (mem_range.mp hd)]

theorem labeledEntry_card_le (M nx ny : ℕ) :
    Fintype.card (LabeledEntry M nx ny) ≤ labeledStateCount M nx ny := by
  rw [Fintype.card_prod, physicalNode_card]
  exact Nat.mul_le_mul_left _ (targetInterval_card_le ny)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineLocality
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal query-filtered online loop has at most one candidate per scale. -/

namespace EditApproximation

open Finset

theorem makeTargetState_endpoints {n lo hi : ℕ} {q : TargetInterval n}
    (h : makeTargetState n lo hi = some q) : q.lo = lo ∧ q.hi = hi := by
  unfold makeTargetState at h
  split_ifs at h with hv
  · cases h
    exact ⟨rfl, rfl⟩

theorem targetStates_nodup (n : ℕ) : (targetStates n).Nodup := by
  unfold targetStates
  apply List.nodup_flatMap.mpr
  constructor
  · intro lo _
    apply (List.nodup_range (n := n + 1)).filterMap
    intro hi hi' q hq hq'
    have h := (makeTargetState_endpoints (Option.mem_def.mp hq)).2
    have h' := (makeTargetState_endpoints (Option.mem_def.mp hq')).2
    exact h.symm.trans h'
  · apply (List.nodup_range (n := n + 1)).imp
    intro lo lo' hne q hq hq'
    obtain ⟨hi, _, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨hi', _, hq'⟩ := List.mem_filterMap.mp hq'
    exact hne ((makeTargetState_endpoints hq).1.symm.trans (makeTargetState_endpoints hq').1)

theorem dyadicScales_nodup (N : ℕ) : (dyadicScales N).Nodup :=
  (List.nodup_range (n := Nat.log 2 N + 1)).map (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))

theorem representativeList_nodup {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) : (representativeList N P F a initial).Nodup := by
  unfold representativeList
  apply List.nodup_flatMap.mpr
  constructor
  · intro b _
    exact ((targetStates_nodup n).filter _).map (fun _ _ heq => congrArg Prod.snd heq)
  · apply (dyadicScales_nodup N).imp
    intro b b' hne pair hp hp'
    obtain ⟨r, _, heq⟩ := List.mem_map.mp hp
    obtain ⟨r', _, heq'⟩ := List.mem_map.mp hp'
    exact hne ((congrArg Prod.fst heq).trans (congrArg Prod.fst heq').symm)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation




theorem dyadicSeedExponent_active (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    f < dyadicSeedExponent f initial pass := by
  have hd : 0 < f - 2 := by omega
  have hproduct : (f - 2) * pass < initial - f := by
    by_contra hn
    have hle : dyadicSeedPassCount f initial ≤ pass :=
      (ceilDiv_le_iff_le_mul hd).2 (le_of_not_gt hn)
    omega
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedExponent_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ f := by
  have hd : 0 < f - 2 := by omega
  have hproduct : initial - f ≤ (f - 2) * dyadicSeedPassCount f initial :=
    (ceilDiv_le_iff_le_mul hd).1 le_rfl
  unfold dyadicSeedExponent
  rw [Nat.mul_comm] at hproduct
  omega

theorem dyadicSeedExponent_succ (f initial pass : ℕ) :
    dyadicSeedExponent f initial (pass + 1) = dyadicSeedExponent f initial pass - (f - 2) := by
  simp only [dyadicSeedExponent, Nat.add_mul, one_mul, Nat.sub_sub]

theorem dyadicSeedFactor_integer (f initial pass : ℕ) (hf : 3 ≤ f)
    (hpass : pass < dyadicSeedPassCount f initial) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial pass) (2 ^ f) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
  have hactive := dyadicSeedExponent_active f initial pass hf hpass
  have hquotient : (2 : ℚ) ^ dyadicSeedExponent f initial pass / ((2 ^ f : ℕ) : ℚ) =
      ((2 ^ (dyadicSeedExponent f initial pass - f) : ℕ) : ℚ) := by
    push_cast
    apply (div_eq_iff (pow_ne_zero f (by norm_num : (2 : ℚ) ≠ 0))).2
    rw [← pow_add, Nat.sub_add_cancel hactive.le]
  unfold refinementFactor
  rw [hquotient, max_eq_right]
  exact_mod_cast Nat.one_le_two_pow (n := dyadicSeedExponent f initial pass - f)

theorem dyadicSeedFactor_bound (f initial pass : ℕ) :
    (2 : ℚ) ^ dyadicSeedExponent f initial pass ≤ (2 : ℚ) ^ initial :=
  pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

theorem dyadicSeedFactor_terminal (f initial : ℕ) (hf : 3 ≤ f) :
    (2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial) ≤ (2 ^ f : ℕ) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (dyadicSeedExponent_terminal f initial hf)

theorem dyadicSeedFactor_terminal_refinement (f initial : ℕ) (hf : 3 ≤ f) :
    refinementFactor ((2 : ℚ) ^ dyadicSeedExponent f initial (dyadicSeedPassCount f initial)) (2 ^ f) = 1 := by
  unfold refinementFactor
  apply max_eq_left
  apply (div_le_one (by positivity : (0 : ℚ) < (2 ^ f : ℕ))).2
  exact dyadicSeedFactor_terminal f initial hf





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

theorem physicalOnlineRawKey_injective :
    Function.Injective (physicalOnlineRawKey source target U N P F A) := by
  rintro ⟨node, representative⟩ ⟨node', representative'⟩ heq
  have hnode := congrArg Prod.fst heq
  change node = node' at hnode
  subst node'
  have hscale := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length =>
    (dyadicScales N).get key.2.1) heq
  have hcenter := congrArg (fun key : PhysicalLocalOnlineKey M J N target.length => key.2.2) heq
  simp only [physicalOnlineRawKey, physicalScaleIndex_get] at hscale hcenter
  have hrep := (representativeList_nodup N P F _ _).injective_get (Prod.ext hscale hcenter)
  cases hrep
  rfl

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem list_eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] (items : List α) :
    items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons first rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, list_eraseDups_nodup _⟩
    intro hmem
    have hfalse := (List.mem_filter.mp (List.mem_eraseDups.mp hmem)).2
    simp at hfalse
termination_by items.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun item => !(item == first)) rest)



section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent : ℕ) (A : ℚ)

theorem physicalGroupRawKey_injective :
    Function.Injective (physicalGroupRawKey source target U N P F exponent A) := by
  rintro ⟨node, scale, cell⟩ ⟨node', scale', cell'⟩ heq
  have hn := congrArg Prod.fst heq
  change node = node' at hn
  subst node'
  have hs := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.1) heq
  change scale = scale' at hs
  subst scale'
  have hlo := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.1.val) heq
  have hhi := congrArg (fun key : PhysicalLocalGroupKey M J N target.length exponent => key.2.2.2.val) heq
  simp only [physicalGroupRawKey] at hlo hhi
  have hnodup : (physicalProgramCells source target U N P F A exponent node.1
      ((dyadicScales N).get scale)).Nodup := list_eraseDups_nodup _
  have hcell := hnodup.injective_get (Prod.ext hlo hhi)
  cases hcell
  rfl

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau : ℚ)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalLocalProgramOldKey_injective :
    Function.Injective (physicalLocalProgramOldKey source target U N P F A exponent) := by
  intro first second heq
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      exact congrArg Sum.inl
        (physicalOnlineRawKey_injective source target U N P F A (Sum.inl.inj heq))
    | inr second => exact False.elim (Sum.inl_ne_inr heq)
  | inr first =>
    cases second with
    | inl second => exact False.elim (Sum.inr_ne_inl heq)
    | inr second =>
      exact congrArg Sum.inr
        (physicalGroupRawKey_injective source target U N P F exponent A (Sum.inr.inj heq))

variable (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)

theorem physicalLocalProgramDrawLaw_map :
    (physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau).map
      (physicalLocalProgramToComplete source target U N P F A T exponent H Q tau hsize hP hF hA hseed) =
    physicalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau := by
  have hmap := finite_pi_restrict_image_map
    (physicalLocalProgramCoordinateLaw (R := R) source target U N P F A T exponent H Q tau)
    (physicalLocalProgramOldKey source target U N P F A exponent)
    (physicalLocalProgramOldKey_injective source target U N P F A exponent)
    (physicalLocalProgramCoordinateImage source target U N P F A T exponent H Q tau hsize hP hF hA hseed)
    (fun _ => measurable_of_finite _)
  refine hmap.trans ?_
  unfold physicalProgramDrawLaw
  congr 1
  funext key
  cases key with
  | inl online =>
    exact finite_uniform_array_cast R _ _
      (physicalLocalOnlineMass_on_key source target U N P F A T exponent H tau hsize hP hF hA hseed online)
  | inr group => exact Measure.map_id

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveSeedLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh streams indexed by every possible incoming seed make adaptive
seed-dependent draw types compatible with a single finite product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_integral_test {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (test : Ω → Prop) [DecidablePred test] :
    (∫ ω, if test ω then (1 : ℝ) else 0 ∂μ) = μ.real {ω | test ω} := by
  have h := integral_indicator_one (μ := μ) (Set.toFinite {ω | test ω}).measurableSet
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using h

section Step

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]

theorem adaptiveSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) (good nextGood : Seed → Prop)
    [DecidablePred good] [DecidablePred nextGood] (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ seed, good seed → (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ q) :
    (adaptiveSeedLaw drawLaw incoming next).real {seed | ¬ nextGood seed} ≤
      incoming.real {seed | ¬ good seed} + q := by
  classical
  rw [adaptiveSeedLaw, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  change (incoming.prod (Measure.pi drawLaw)).real
    {pair : Seed × (∀ seed, Draw seed) | ¬ nextGood (next pair.1 (pair.2 pair.1))} ≤ _
  rw [← finite_integral_test (incoming.prod (Measure.pi drawLaw))
    (fun pair : Seed × (∀ seed, Draw seed) => ¬ nextGood (next pair.1 (pair.2 pair.1)))]
  change (∫ pair : Seed × (∀ seed, Draw seed),
    if ¬ nextGood (next pair.1 (pair.2 pair.1)) then (1 : ℝ) else 0
      ∂incoming.prod (Measure.pi drawLaw)) ≤ _
  rw [integral_prod _ (.of_finite)]
  have hinner (seed : Seed) :
      (∫ draws : ∀ seed, Draw seed, if ¬ nextGood (next seed (draws seed)) then (1 : ℝ) else 0
        ∂Measure.pi drawLaw) = (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} := by
    rw [integral_comp_eval (μ := drawLaw) (i := seed)
      (f := fun draw => if ¬ nextGood (next seed draw) then (1 : ℝ) else 0)
      (measurable_of_finite _).aestronglyMeasurable]
    exact finite_integral_test _ _
  simp_rw [hinner]
  have hpoint (seed : Seed) : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤
      (if ¬ good seed then (1 : ℝ) else 0) + q := by
    by_cases hg : good seed
    · simpa only [hg, not_true_eq_false, ite_false, if_false, zero_add] using hstep seed hg
    · have hprob : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ 1 := measureReal_le_one
      simpa only [hg, not_false_eq_true, ite_true, if_true] using hprob.trans (le_add_of_nonneg_right hq)
  have h := integral_mono (μ := incoming) (.of_finite) (.of_finite) hpoint
  rw [integral_add (.of_finite) (integrable_const _), finite_integral_test,
    integral_const, probReal_univ, one_smul] at h
  exact h

end Step

section Sequence

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type*} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (incoming : Measure Seed) (next : ∀ pass seed, Draw pass seed → Seed)

theorem adaptiveSeedSequence_failure [IsProbabilityMeasure incoming]
    (good : ℕ → Seed → Prop) [∀ pass, DecidablePred (good pass)]
    (q : ℕ → ℝ) (hq : ∀ pass, 0 ≤ q pass) (passes : ℕ)
    (hstep : ∀ pass < passes, ∀ seed, good pass seed →
      (drawLaw pass seed).real {draw | ¬ good (pass + 1) (next pass seed draw)} ≤ q pass) :
    (adaptiveSeedSequence drawLaw incoming next passes).real {seed | ¬ good passes seed} ≤
      incoming.real {seed | ¬ good 0 seed} + ∑ pass ∈ Finset.range passes, q pass := by
  induction passes with
  | zero => simp only [adaptiveSeedSequence, Finset.sum_range_zero, add_zero, le_refl]
  | succ passes ih =>
    have hprevious := ih (fun pass hp seed hg => hstep pass (by omega) seed hg)
    have hnext := adaptiveSeedLaw_failure (drawLaw passes)
      (adaptiveSeedSequence drawLaw incoming next passes) (next passes)
      (good passes) (good (passes + 1)) (q passes) (hq passes)
      (hstep passes (by omega))
    apply hnext.trans
    rw [Finset.sum_range_succ]
    linarith only [hprevious]

end Sequence

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedPassNumerics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical amplification for the literal H²-copy seed update and
the finite sequence of refinement passes. -/

namespace EditApproximation

theorem seed_copy_binary_tail (copies ell : ℕ) (hell : 64 ≤ ell) :
    (2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2) ≤
      Real.exp (-(copies : ℝ)) := by
  let k := copies - copies / 2
  have hcopies : copies ≤ 2 * k := by dsimp only [k]; omega
  have hellR : (64 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellpos : (0 : ℝ) < ell := by linarith only [hellR]
  have hscale : (4 : ℝ) / ell ≤ 1 / 16 := by
    apply (div_le_iff₀ hellpos).2
    linarith only [hellR]
  have hexp2 : Real.exp (2 : ℝ) ≤ 16 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have he := Real.exp_one_lt_three
    have hep := Real.exp_pos (1 : ℝ)
    nlinarith only [he, hep]
  have hexpinv : (1 / 16 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hexp2
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * (1 / (ell : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcopies) (by positivity)
    _ = ((4 : ℝ) / ell) ^ k := by rw [pow_mul, ← mul_pow]; congr 1; norm_num [div_eq_mul_inv]
    _ ≤ (1 / 16 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hscale k
    _ ≤ Real.exp (-2) ^ k := pow_le_pow_left₀ (by norm_num) hexpinv k
    _ = Real.exp (-2 * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(copies : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hc : (copies : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hcopies
      linarith only [hc]

theorem seed_state_union_numeric (H domain : ℝ)
    (hdomain : domain ≤ Real.exp (10 * H)) :
    domain * Real.exp (-(H ^ 2)) ≤ Real.exp (10 * H - H ^ 2) := by
  calc
    _ ≤ Real.exp (10 * H) * Real.exp (-(H ^ 2)) :=
      mul_le_mul_of_nonneg_right hdomain (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1

theorem seed_pass_union_numeric (H : ℝ) (hH : 100 ≤ H) :
    H * Real.exp (10 * H - H ^ 2) ≤ 1 / 100 := by
  have hH0 : 0 ≤ H := by linarith only [hH]
  have hquadratic := mul_nonneg hH0 (show 0 ≤ H - 100 by linarith only [hH])
  have hexponent : 10 * H - H ^ 2 ≤ -2 * H := by nlinarith only [hquadratic, hH]
  have hHexp : H ≤ Real.exp H := by linarith only [Real.add_one_le_exp H]
  have hexp100 : (100 : ℝ) ≤ Real.exp H := hH.trans hHexp
  calc
    _ ≤ H * Real.exp (-2 * H) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hH0
    _ ≤ Real.exp H * Real.exp (-2 * H) := mul_le_mul_of_nonneg_right hHexp (Real.exp_pos _).le
    _ = Real.exp (-H) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 / 100 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hexp100

theorem computed_seed_total_failure (N passes : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hpasses : passes ≤ inputHeight N) :
    (1 / 100 : ℝ) + passes * Real.exp (10 * inputHeight N - (inputHeight N : ℝ) ^ 2) < 1 / 10 := by
  have hlogs := inputSmallLog_bounds N hN
  have hheight : 7 ≤ heightExponent N := by omega
  have hH100 : 100 ≤ inputHeight N := (by norm_num : 100 ≤ (2 : ℕ) ^ 7).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hheight)
  have hpassR : (passes : ℝ) ≤ inputHeight N := by exact_mod_cast hpasses
  have hbound := (mul_le_mul_of_nonneg_right hpassR
    (Real.exp_pos (10 * inputHeight N - (inputHeight N : ℝ) ^ 2)).le).trans
    (seed_pass_union_numeric (inputHeight N) (by exact_mod_cast hH100))
  linarith only [hbound]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_positive_counts (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    0 < (integerParameters N).T ∧ 0 < (integerParameters N).S := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpow := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hpowN : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpow
  have hellpos : 0 < inputSmallLog N := Nat.two_pow_pos _
  exact ⟨Nat.two_pow_pos _, Nat.div_pos hpowN (pow_pos hellpos 2)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_Amplification
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent-copy amplification for the seed passes

The tail estimate is the direct finite-subset argument from Section 8.
Independence is used only between copies at a fixed state. The subsequent
union bound over states makes no independence assumption between states.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

theorem independent_failure_subset_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (copies : Finset ι) (q : ℝ)
    (hbad : ∀ i ∈ copies, μ.real (bad i) ≤ q) :
    μ.real (⋂ i ∈ copies, bad i) ≤ q ^ copies.card := by
  rw [measureReal_def, hindep.meas_biInter, ENNReal.toReal_prod]
  have hprod := Finset.prod_le_prod (fun i _ => measureReal_nonneg) hbad
  simpa only [prod_const, measureReal_def] using hprod

theorem independent_failure_count_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (k : ℕ) (q : ℝ)
    (hbad : ∀ i, μ.real (bad i) ≤ q) :
    μ.real {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ≤
      (Fintype.card ι).choose k * q ^ k := by
  classical
  let subsets := (univ : Finset ι).powersetCard k
  have hcover : {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ⊆
      ⋃ s ∈ subsets, ⋂ i ∈ s, bad i := by
    intro ω hω
    obtain ⟨s, hsub, hcard⟩ := exists_subset_card_eq hω
    have hs : s ∈ subsets := mem_powersetCard.mpr
      ⟨fun i hi => mem_univ i, hcard⟩
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨hs, ?_⟩⟩
    exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi => (mem_filter.mp (hsub hi)).2
  apply (measureReal_mono (μ := μ) hcover (measure_ne_top μ _)).trans
  apply (measureReal_biUnion_finset_le subsets _).trans
  have hbound (s : Finset ι) (hs : s ∈ subsets) :
      μ.real (⋂ i ∈ s, bad i) ≤ q ^ k := by
    have hcard := (mem_powersetCard.mp hs).2
    simpa only [hcard] using independent_failure_subset_bound μ bad hindep s q (fun i _ => hbad i)
  have hsum := sum_le_sum hbound
  simpa only [sum_const, nsmul_eq_mul, subsets, card_powersetCard, card_univ] using hsum

theorem independent_failure_count_binary_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ι → Set Ω)
    (hindep : iIndepSet bad μ) (k : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hbad : ∀ i, μ.real (bad i) ≤ q) :
    μ.real {ω | k ≤ (univ.filter fun i => ω ∈ bad i).card} ≤
      (2 : ℝ) ^ Fintype.card ι * q ^ k := by
  apply (independent_failure_count_bound μ bad hindep k q hbad).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq k)
  exact_mod_cast Nat.choose_le_two_pow (Fintype.card ι) k

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_Median
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable upper middle order statistic

The seed pass sorts its integer copy outputs and takes index `length/2`.
Strictly more than half the outputs below an upper bound suffice; ties
and repeated values are retained by the list representation.
-/

namespace EditApproximation



theorem upperMedian_upper (values : List ℕ) (hvalues : values ≠ []) (upper : ℕ)
    (hmajority : values.length / 2 < values.countP (fun value => value ≤ upper)) :
    upperMedian values ≤ upper := by
  let sorted := values.mergeSort (· ≤ ·)
  have hlength : sorted.length = values.length := List.length_mergeSort values
  have hpositive : 0 < values.length := List.length_pos_iff.mpr hvalues
  have hindex : values.length / 2 < sorted.length := by omega
  have hmedian : upperMedian values = sorted[values.length / 2] :=
    (List.getElem_eq_getD 0).symm
  by_contra hnot
  have habove : upper < sorted[values.length / 2] := by omega
  have hdrop : (sorted.drop (values.length / 2)).filter (fun value => value ≤ upper) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value hvalue
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hvalue
    have hj' : values.length / 2 + j < sorted.length := by
      simp only [List.length_drop] at hj
      omega
    have hge : sorted[values.length / 2] ≤ sorted[values.length / 2 + j] :=
      (List.sortedLE_mergeSort (l := values)).getElem_le_getElem_of_le
        (hi := hindex) (hj := hj')
        (show values.length / 2 ≤ values.length / 2 + j by omega)
    have hget : (sorted.drop (values.length / 2))[j] = sorted[values.length / 2 + j] := by
      simp only [List.getElem_drop]
    rw [hget] at heq
    have haboveValue : upper < value := habove.trans_le (hge.trans_eq heq)
    simpa only [decide_eq_true_eq] using not_le_of_gt haboveValue
  have hdropCount : (sorted.drop (values.length / 2)).countP (fun value => value ≤ upper) = 0 := by
    rw [List.countP_eq_length_filter, hdrop]
    rfl
  have hcount : sorted.countP (fun value => value ≤ upper) ≤ values.length / 2 := by
    have hsplit := List.take_append_drop (values.length / 2) sorted
    rw [← hsplit, List.countP_append, hdropCount, Nat.add_zero]
    exact List.countP_le_length.trans (List.length_take_le _ _)
  have hperm := (List.mergeSort_perm values (· ≤ ·)).countP_eq (fun value => value ≤ upper)
  change sorted.countP (fun value => value ≤ upper) = values.countP (fun value => value ≤ upper) at hperm
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedMedian
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed update uses the actual integer ceilings, upper median and clamp.
Copies share an entire table within each run and are independent between runs. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem ofFn_countP_filter {β : Type*} {copies : ℕ} (output : Fin copies → β) (p : β → Bool) :
    (List.ofFn output).countP p = (univ.filter fun i => p (output i)).card := by
  rw [List.ofFn_eq_map, List.countP_map]
  simpa only [List.toFinset_finRange, Bool.decide_eq_true, Function.comp_def] using
    ((List.nodup_finRange copies).card_eq_countP (P := fun i => p (output i))).symm

theorem finiteMedianSeed_upper {Ω : Type*} (N copies upper : ℕ) (hcopies : 0 < copies)
    (output : Ω → ℕ) (draws : Fin copies → Ω)
    (hfew : (univ.filter fun i => upper < output (draws i)).card < copies - copies / 2) :
    finiteMedianSeed N copies output draws ≤ upper := by
  apply (min_le_right _ _).trans
  apply upperMedian_upper _ (by simpa using hcopies.ne')
  rw [List.length_ofFn, ofFn_countP_filter]
  simp only [decide_eq_true_eq]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin copies)))
    (p := fun i => upper < output (draws i))
  simp only [card_univ, Fintype.card_fin, not_lt] at hsum
  omega

theorem finiteMedianSeed_failure_bound {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N copies upper : ℕ) (hcopies : 0 < copies)
    (output : Ω → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hsingle : μ.real {ω | upper < output ω} ≤ q) :
    (Measure.pi fun _ : Fin copies => μ).real
      {draws | upper < finiteMedianSeed N copies output draws} ≤
      (2 : ℝ) ^ copies * q ^ (copies - copies / 2) := by
  classical
  let bad : Fin copies → Set (Fin copies → Ω) := fun i => {draws | upper < output (draws i)}
  have hindepFun : iIndepFun (fun i (draws : Fin copies → Ω) => draws i)
      (Measure.pi fun _ : Fin copies => μ) :=
    iIndepFun_pi (μ := fun _ : Fin copies => μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hindep : iIndepSet bad (Measure.pi fun _ : Fin copies => μ) := by
    apply (iIndepSet_iff_meas_biInter (fun _ => (Set.toFinite _).measurableSet)).2
    intro s
    exact hindepFun.meas_biInter (fun i _ =>
      ⟨{ω | upper < output ω}, (Set.toFinite _).measurableSet, rfl⟩)
  have hbad (i : Fin copies) : (Measure.pi fun _ : Fin copies => μ).real (bad i) ≤ q := by
    have hmap := measurePreserving_eval (fun _ : Fin copies => μ) i
    have heq := hmap.measure_preimage ((Set.toFinite {ω | upper < output ω}).measurableSet.nullMeasurableSet)
    have heq' : (Measure.pi fun _ : Fin copies => μ) (bad i) = μ {ω | upper < output ω} := by
      simpa only [bad, Function.eval, Set.preimage, Set.mem_ofPred_eq] using heq
    unfold Measure.real
    rw [heq']
    exact hsingle
  have htail := independent_failure_count_binary_bound (Measure.pi fun _ : Fin copies => μ)
    bad hindep (copies - copies / 2) q hq hbad
  apply (measureReal_mono (μ := Measure.pi fun _ : Fin copies => μ) ?_ (measure_ne_top _ _)).trans
    (by simpa only [Fintype.card_fin] using htail)
  intro draws hfail
  by_contra hfew
  have hfew' : ¬ copies - copies / 2 ≤ (univ.filter fun i => upper < output (draws i)).card := by
    simpa only [bad, Set.mem_ofPred_eq] using hfew
  have hupper := finiteMedianSeed_upper N copies upper hcopies output draws (lt_of_not_ge hfew')
  exact (not_lt_of_ge hupper) hfail

theorem finite_positive_excess_tail {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (value : Ω → ℚ) (c : ℕ) (hc : 0 < c)
    (ell : ℝ) (_hell : 0 < ell)
    (hexcess : (∫ ω, max ((value ω : ℝ) - c) 0 ∂μ) ≤ (1 / ell) * c) :
    μ.real {ω | 2 * (c : ℚ) < value ω} ≤ 1 / ell := by
  let excess := fun ω => max ((value ω : ℝ) - c) 0
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => le_max_right ((value ω : ℝ) - c) 0))
    (show Integrable excess μ from .of_finite) (c : ℝ)
  have hcr : (0 : ℝ) < c := Nat.cast_pos.2 hc
  have htail : μ.real {ω | (c : ℝ) ≤ excess ω} ≤ 1 / ell := by
    apply (mul_le_mul_iff_left₀ hcr).mp
    simpa only [mul_comm] using hmarkov.trans hexcess
  apply (measureReal_mono (μ := μ) ?_).trans htail
  intro ω hω
  have hR : 2 * (c : ℝ) < value ω := by exact_mod_cast hω
  exact (by dsimp only [excess]; exact (by linarith : (c : ℝ) ≤ (value ω : ℝ) - c).trans (le_max_left _ _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedPass
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full-table median seed pass from independent refinement copies under finite Bernstein bounds. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Pass

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T S : ℕ) (hTeq : T = (integerParameters N).T) (hSeq : S = (integerParameters N).S)
  (hHeq : H = inputHeight N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (a copies : ℕ) (ha : (a : ℚ) = refinementFactor A (inputSmallLog N)) (hcopies : 0 < copies)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "law" => physicalProgramDrawLaw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "copyLaw" => Measure.pi (fun _ : Fin copies => law)
local notation "update" => physicalMedianUpdate source target U N P ell A T delta a S copies choices

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_state_failure (state : PhysicalEntry M J target.length) :
    (copyLaw).real {draws | 2 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state} ≤
      (2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2) := by
  classical
  let c := stateEditCost (physicalSource source state.1) target state.2
  let value : Draw → ℚ := fun draw => physicalRefinement source target U N P ell A T delta (choices draw) state.1 S state.2
  let output : Draw → ℕ := fun draw => physicalScaledCopy source target U N P ell A T delta a S (choices draw) state
  have hbranch : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hP := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hT : 0 < T := by rw [hTeq]; exact (computed_stage_positive_counts N hN hell).1
  have haQ : (0 : ℚ) < a := by
    rw [ha]
    exact lt_of_lt_of_le zero_lt_one (refinementFactor_spec A ell (by omega)).1
  have hsingle : (law).real {draw | 2 * a * c < output draw} ≤ 1 / (ell : ℝ) := by
    by_cases hzero : c = 0
    · have hout (draw : Draw) : output draw = 0 := by
        have hz := physicalRefinement_zero_cost source target hbranch U N P ell A hsize hP hF hA hseed
          T hT delta (choices draw) state.1 S state.2 hzero
        simp only [output, physicalScaledCopy, hz, mul_zero, Nat.ceil_zero]
      simp only [hzero, mul_zero, hout, lt_self_iff_false, Set.ofPred_false, measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · have hexcess := physicalProgram_expected_state_excess (R := R) source target N hN hell hMeq hJeq
        U P hPeq A hA hAupper hsize hseed T S hTeq hSeq hHeq bernstein state.1 state.2
      have hraw := finite_positive_excess_tail law value c (Nat.pos_of_ne_zero hzero)
        (ell : ℝ) (Nat.cast_pos.2 (Nat.two_pow_pos _)) hexcess
      apply (measureReal_mono (μ := law) ?_ (measure_ne_top _ _)).trans hraw
      intro draw hbad
      by_contra hnot
      have hvalue : value draw ≤ 2 * c := le_of_not_gt hnot
      have hround : output draw ≤ 2 * a * c := by
        apply Nat.ceil_le.mpr
        have hm := mul_le_mul_of_nonneg_left hvalue haQ.le
        push_cast
        nlinarith only [hm]
      exact (not_lt_of_ge hround) hbad
  exact finiteMedianSeed_failure_bound law N copies (2 * a * c) hcopies output
    (1 / (ell : ℝ)) (div_nonneg zero_le_one (Nat.cast_nonneg _)) hsingle

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_all_failure :
    (copyLaw).real {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ≤
      Fintype.card (PhysicalEntry M J target.length) *
        ((2 : ℝ) ^ copies * (1 / (ell : ℝ)) ^ (copies - copies / 2)) := by
  classical
  let bad := fun state : PhysicalEntry M J target.length =>
    {draws : Fin copies → Draw | 2 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state}
  have hcover : {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ⊆ ⋃ state, bad state := by
    intro draws hfail
    obtain ⟨state, hstate⟩ := not_forall.mp hfail
    apply Set.mem_iUnion.mpr
    refine ⟨state, ?_⟩
    have hlower := physicalMedianUpdate_lower (R := R) source target N hN hell U P hPeq A hA
      hsize hseed T S hTeq a copies ha hcopies draws state
    have hu : 4 * a * stateEditCost (physicalSource source state.1) target state.2 < update draws state := by
      exact lt_of_not_ge (fun h => hstate ⟨hlower, h⟩)
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right a (by decide : 2 ≤ 4))) hu
  apply (measureReal_mono (μ := copyLaw) hcover (measure_ne_top _ _)).trans
  apply (measureReal_iUnion_fintype_le bad).trans
  have hsum := sum_le_sum (fun state (_ : state ∈ (univ : Finset (PhysicalEntry M J target.length))) =>
    physicalMedianUpdate_state_failure (R := R) source target N hN hell hMeq hJeq U P hPeq A hA hAupper
      hsize hseed T S hTeq hSeq hHeq bernstein a copies ha hcopies state)
  simpa only [sum_const, card_univ, nsmul_eq_mul] using hsum

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein ha hcopies in
 theorem physicalMedianUpdate_computed_failure (hcopiesEq : copies = H ^ 2) :
    (copyLaw).real {draws | ¬ ∀ state : PhysicalEntry M J target.length,
      stateEditCost (physicalSource source state.1) target state.2 ≤ update draws state ∧
      update draws state ≤ 4 * a * stateEditCost (physicalSource source state.1) target state.2} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ ell := by omega
  have hcard : Fintype.card (PhysicalEntry M J target.length) ≤ labeledStateCount M source.length target.length := by
    rw [hJeq]
    exact labeledEntry_card_le M source.length target.length
  have hcardR : (Fintype.card (PhysicalEntry M J target.length) : ℝ) ≤ Real.exp (10 * H) := by
    apply (Nat.cast_le.mpr hcard).trans
    rw [hMeq, hHeq]
    exact computed_labeledStateCount_exp N source.length target.length hN (by omega) (by omega) hcut
  have htail := seed_copy_binary_tail copies ell (by omega : 64 ≤ ell)
  have hbound := physicalMedianUpdate_all_failure (R := R) source target N hN hell hMeq hJeq U P hPeq
    A hA hAupper hsize hseed T S hTeq hSeq hHeq bernstein a copies ha hcopies
  apply hbound.trans
  apply (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)).trans
  rw [hcopiesEq, Nat.cast_pow]
  exact seed_state_union_numeric (H : ℝ) (Fintype.card (PhysicalEntry M J target.length) : ℝ) hcardR

end Pass

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedTables
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite clamped seed tables and the exact table returned by a median pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem physicalMedianUpdateTable_good_iff {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω) :
    physicalSeedGood source target (4 * a : ℚ)
      (physicalMedianUpdateTable source target U N P F A T delta a S copies choices draws) ↔
      ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          physicalMedianUpdate source target U N P F A T delta a S copies choices draws state ∧
        physicalMedianUpdate source target U N P F A T delta a S copies choices draws state ≤
          4 * a * stateEditCost (physicalSource source state.1) target state.2 := by
  unfold physicalSeedGood
  simp only [physicalMedianUpdateTable_value]
  constructor
  · intro h state
    exact ⟨(h state).1, by exact_mod_cast (h state).2⟩
  · intro h state
    exact ⟨(h state).1, by exact_mod_cast (h state).2⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual finite adaptive sequence of median seed passes. Every chosen
incoming table uses its own fresh product of full-table copy streams. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem scheduledSeedMultiplier_spec (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass < computedSeedPassCount N) :
    (scheduledSeedMultiplier N pass : ℚ) = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) := by
  unfold scheduledSeedMultiplier scheduledSeedFactor
  simpa only [inputSmallLog] using
    (dyadicSeedFactor_integer (smallLogExponent N) (computedSeedInitialExponent N) pass hf hpass).symm

theorem scheduledSeedFactor_succ (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass < computedSeedPassCount N) :
    scheduledSeedFactor N (pass + 1) = 4 * (scheduledSeedMultiplier N pass : ℚ) := by
  have hactive := dyadicSeedExponent_active (smallLogExponent N) (computedSeedInitialExponent N) pass hf hpass
  have heq : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) (pass + 1) =
      (dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N) + 2 := by
    rw [dyadicSeedExponent_succ]
    omega
  unfold scheduledSeedFactor scheduledSeedMultiplier
  rw [heq, pow_add]
  push_cast
  norm_num
  ring

theorem scheduledSeedFactor_zero (N : ℕ) :
    scheduledSeedFactor N 0 = ((integerParameters N).initialFactor : ℚ) := by
  simpa only [scheduledSeedFactor, dyadicSeedExponent, zero_mul, Nat.sub_zero] using computedSeed_initial_factor N

theorem scheduledSeedFactor_terminal_refinement (N : ℕ) (hf : 3 ≤ smallLogExponent N) :
    refinementFactor (scheduledSeedFactor N (computedSeedPassCount N)) (inputSmallLog N) = 1 := by
  exact dyadicSeedFactor_terminal_refinement (smallLogExponent N) (computedSeedInitialExponent N) hf

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
 theorem scheduledSeedNext_failure (pass : ℕ) (hpass : pass < computedSeedPassCount N)
    (seed : Seed) (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed) :
    (scheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (scheduledSeedNext (R := R) source target N P T S H pass seed draw)} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hA : (1 : ℚ) ≤ scheduledSeedFactor N pass := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  have hAupper : scheduledSeedFactor N pass ≤ ((integerParameters N).initialFactor : ℚ) := by
    unfold scheduledSeedFactor
    rw [← computedSeed_initial_factor]
    exact dyadicSeedFactor_bound _ _ _
  have hcopies : 0 < H ^ 2 := by rw [hHeq]; exact pow_pos (Nat.two_pow_pos _) 2
  have h := physicalMedianUpdate_computed_failure (R := R) source target N hN hell hMeq hJeq
    (clampedSeedNat seed) P hPeq (scheduledSeedFactor N pass) hA hAupper hsize hseed T S hTeq hSeq hHeq
    bernstein (scheduledSeedMultiplier N pass) (H ^ 2) (scheduledSeedMultiplier_spec N pass hf hpass) hcopies rfl
  have hevents : {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (scheduledSeedNext (R := R) source target N P T S H pass seed draw)} =
      {draw : ScheduledSeedDraw (R := R) source target N P T H pass seed | ¬ ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          physicalMedianUpdate source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
            T delta (scheduledSeedMultiplier N pass) S (H ^ 2)
            (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
              T thetaExponent H (ell ^ 80) tau eta kappa) draw state ∧
        physicalMedianUpdate source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
            T delta (scheduledSeedMultiplier N pass) S (H ^ 2)
            (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
              T thetaExponent H (ell ^ 80) tau eta kappa) draw state ≤
          4 * scheduledSeedMultiplier N pass * stateEditCost (physicalSource source state.1) target state.2} := by
    ext draw
    rw [scheduledSeedFactor_succ N pass hf hpass]
    exact not_congr (physicalMedianUpdateTable_good_iff _ _ _ _ _ _ _ _ _ _ _ _ _ draw)
  rw [hevents]
  exact h

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSchedule
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed schedule run with bounded local random keys. A whole incoming
seed chooses one fresh product of full-copy local streams. The failure
bound follows from the actual local median law, rather than a seed oracle. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedNext_failure (pass : ℕ) (hpass : pass < computedSeedPassCount N)
    (seed : Seed) (hseed : physicalSeedGood source target (scheduledSeedFactor N pass) seed) :
    (localScheduledSeedDrawLaw (R := R) source target N P T H pass seed).real
      {draw | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1))
        (localScheduledSeedNext (R := R) source target N P T S H pass seed draw)} ≤
      Real.exp (10 * H - (H : ℝ) ^ 2) := by
  have hevent := localScheduledSeedNext_event (R := R) source target N P T S H hN hPeq hsize
    pass seed hseed {next | ¬ physicalSeedGood source target (scheduledSeedFactor N (pass + 1)) next}
  simp only [Set.mem_ofPred_eq] at hevent
  rw [hevent]
  exact scheduledSeedNext_failure source target N P T S H hN hell hMeq hJeq hPeq hTeq hSeq hHeq
    hsize bernstein pass hpass seed hseed

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming] :
    (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} ≤
      incoming.real {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N 0) seed} +
        computedSeedPassCount N * Real.exp (10 * H - (H : ℝ) ^ 2) := by
  classical
  have h := adaptiveSeedSequence_failure
    (localScheduledSeedDrawLaw (R := R) source target N P T H) incoming
    (localScheduledSeedNext (R := R) source target N P T S H)
    (fun pass => physicalSeedGood source target (scheduledSeedFactor N pass))
    (fun _ => Real.exp (10 * H - (H : ℝ) ^ 2)) (fun _ => (Real.exp_pos _).le) (computedSeedPassCount N)
    (fun pass hp seed hg => localScheduledSeedNext_failure source target N P T S H
      hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein pass hp seed hg)
  simpa only [localScheduledSeedLaw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localScheduledSeedLaw_failure_lt (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100) :
    (localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)).real
      {seed | ¬ physicalSeedGood source target (scheduledSeedFactor N (computedSeedPassCount N)) seed} < 1 / 10 := by
  have hbound := localScheduledSeedLaw_failure (R := R) source target N P T S H hN hell hMeq hJeq hPeq
    hTeq hSeq hHeq hsize bernstein incoming
  rw [scheduledSeedFactor_zero] at hbound
  have hsmall : 256 ≤ (2 : ℕ) ^ 1000 := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
    norm_num only [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
    exact h
  have hcut : 200 ≤ ell := by omega
  apply (hbound.trans (add_le_add hinitial le_rfl)).trans_lt
  rw [hHeq]
  exact computed_seed_total_failure N (computedSeedPassCount N) hN hcut
    (computedSeedPassCount_le_height N hN hell)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSeedFinal
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh draw selects the coordinate of the actual incoming seed.
This keeps the dependence of the finite draw type on that table explicit. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {Seed : Type*} [Fintype Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Finite (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]

theorem freshSeed_bad_probability (good : Seed → Prop) :
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | ¬ good pair.1} = incoming.real {seed | ¬ good seed} := by
  classical
  let : Fintype (Seed × (∀ seed, Draw seed)) := Fintype.ofFinite _
  rw [← finite_integral_test (incoming.prod (Measure.pi drawLaw)) (fun pair => ¬ good pair.1)]
  rw [integral_prod _ (.of_finite)]
  change (∫ seed, (∫ _ : ∀ seed, Draw seed, if ¬ good seed then (1 : ℝ) else 0
    ∂Measure.pi drawLaw) ∂incoming) = _
  simp only [integral_const, probReal_univ, one_smul]
  exact finite_integral_test incoming (fun seed => ¬ good seed)

theorem freshSeed_good_excess (good : Seed → Prop) (value : ∀ seed, Draw seed → ℝ)
    (D : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hmoment : ∀ seed, good seed →
      (∫ draw, max (value seed draw - D) 0 ∂drawLaw seed) ≤ (D : ℝ) / ell) :
    (∫ pair, goodExcess {pair : Seed × (∀ seed, Draw seed) | good pair.1}
      (freshSeedValue value) D pair ∂incoming.prod (Measure.pi drawLaw)) ≤ (D : ℝ) / ell := by
  classical
  rw [integral_prod _ (.of_finite)]
  have hinner (seed : Seed) :
      (∫ draws : ∀ seed, Draw seed,
        goodExcess {pair : Seed × (∀ seed, Draw seed) | good pair.1}
          (freshSeedValue value) D (seed, draws) ∂Measure.pi drawLaw) ≤ (D : ℝ) / ell := by
    by_cases hg : good seed
    · simp only [goodExcess, Set.indicator, Set.mem_ofPred_eq, hg, ite_true, if_true,
        freshSeedValue]
      rw [integral_comp_eval (μ := drawLaw) (i := seed)
        (f := fun draw => max (value seed draw - D) 0)
        (measurable_of_finite _).aestronglyMeasurable]
      exact hmoment seed hg
    · simp only [goodExcess, Set.indicator, Set.mem_ofPred_eq, hg, ite_false, if_false,
        integral_zero]
      exact div_nonneg (Nat.cast_nonneg _) hell.le
  have h := integral_mono (μ := incoming) (.of_finite) (integrable_const _) hinner
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem freshSeed_answer_accuracy (good : Seed → Prop) (value : ∀ seed, Draw seed → ℝ)
    {N D : ℕ} {ell epsilon : ℝ} (hDN : D ≤ N) (hD : 0 < D)
    (hell : 0 < ell) (hepsilon : 0 < epsilon) (haccuracy : 10 ≤ ell * epsilon)
    (hseed : incoming.real {seed | ¬ good seed} ≤ 1 / 10)
    (hlower : ∀ seed, good seed → ∀ draw, (D : ℝ) ≤ value seed draw)
    (hmoment : ∀ seed, good seed →
      (∫ draw, max (value seed draw - D) 0 ∂drawLaw seed) ≤ (D : ℝ) / ell) :
    (4 / 5 : ℝ) ≤ (incoming.prod (Measure.pi drawLaw)).real
      {pair | D ≤ integerAnswer N (freshSeedValue value pair) ∧
        (integerAnswer N (freshSeedValue value pair) : ℝ) ≤ (1 + epsilon) * D} := by
  classical
  apply final_answer_accuracy (incoming.prod (Measure.pi drawLaw)) (measurable_of_finite _)
    hDN hD hell hepsilon haccuracy
  · change (incoming.prod (Measure.pi drawLaw)).real {pair | ¬ good pair.1} ≤ 1 / 10
    rw [freshSeed_bad_probability]
    exact hseed
  · intro pair hg
    exact hlower pair.1 hg (pair.2 pair.1)
  · exact .of_finite
  · exact freshSeed_good_excess drawLaw incoming good value D ell hell hmoment

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalFinalAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh bounded-key local query, following the actual local
median schedule, has the required approximation probability. The incoming
law is supplied by the concrete coarse sampler in the final theorem. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localFinalProgramAnswer_equal (rootQ : TargetInterval target.length)
    (heq : source = substring target rootQ.lo rootQ.hi)
    (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
    localFinalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 := by
  simp only [localFinalProgramAnswer, heq, ite_true, if_true]

variable (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
  (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
  (hsize : source.length + target.length ≤ N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

include hN hell hMeq hJeq hPeq hTeq hSeq hHeq hsize bernstein in
theorem localFinalProgram_accuracy_oai (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hinitial : incoming.real {seed | ¬ physicalSeedGood source target
      ((integerParameters N).initialFactor : ℚ) seed} ≤ 1 / 100)
    (rootQ : TargetInterval target.length) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (haccuracy : 10 ≤ (inputSmallLog N : ℝ) * epsilon) :
    (4 / 5 : ℝ) ≤ (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {pair | stateEditCost source target rootQ ≤
        localFinalProgramAnswer (R := R) source target N P T S H rootQ pair ∧
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ pair : ℝ) ≤
          (1 + epsilon) * stateEditCost source target rootQ} := by
  classical
  by_cases heq : source = substring target rootQ.lo rootQ.hi
  · have hcost : stateEditCost source target rootQ = 0 :=
      (EditDistortion.cost_eq_zero_iff (s := true)).mpr heq
    have hans (pair : LocalFinalProgramOutcome (M := M) (J := J) (R := R) source target N P T H) :
        localFinalProgramAnswer (R := R) source target N P T S H rootQ pair = 0 :=
      localFinalProgramAnswer_equal source target N P T S H rootQ heq pair
    simp only [hans, hcost, Nat.cast_zero, mul_zero, le_refl, and_self, Set.ofPred_true, probReal_univ]
    norm_num
  have hD : 0 < stateEditCost source target rootQ :=
    Nat.pos_of_ne_zero (fun h => heq ((EditDistortion.cost_eq_zero_iff (s := true)).mp h))
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hA : (1 : ℚ) ≤ terminalFactor := by
    unfold scheduledSeedFactor
    exact one_le_pow₀ (by norm_num)
  have hAupper : terminalFactor ≤ ((integerParameters N).initialFactor : ℚ) := by
    unfold scheduledSeedFactor
    rw [← computedSeed_initial_factor]
    exact dyadicSeedFactor_bound _ _ _
  have ha := scheduledSeedFactor_terminal_refinement N hf
  have hbranch : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hP := computed_program_grid_lower N P hN hPeq
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hT : 0 < T := by rw [hTeq]; exact (computed_stage_positive_counts N hN hell).1
  have hEll : (0 : ℝ) < ell := Nat.cast_pos.2 (Nat.two_pow_pos _)
  let terminalLaw := localScheduledSeedLaw (R := R) source target N P T S H incoming (computedSeedPassCount N)
  let good : Seed → Prop := physicalSeedGood source target terminalFactor
  let value := localFinalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ
  have hseed : terminalLaw.real {seed | ¬ good seed} ≤ 1 / 10 :=
    (localScheduledSeedLaw_failure_lt (R := R) source target N P T S H hN hell hMeq hJeq hPeq
      hTeq hSeq hHeq hsize bernstein incoming hinitial).le
  have hlower (seed : Seed) (hg : good seed)
      (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) :
      (stateEditCost source target rootQ : ℝ) ≤ value seed draw := by
    rw [show value seed draw = finalProgramValue source target N P T S H rootQ seed
      (physicalLocalProgramToComplete source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg draw) from
      localFinalProgramValue_eq source target N P T S H rootQ seed draw hsize hP hg]
    have h := (physicalRefinement_stage_bounds source target hbranch (clampedSeedNat seed) N P ell
      terminalFactor hsize hP hF hA hg T hT delta
      (physicalProgramDrawSelections source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau eta kappa
        (physicalLocalProgramToComplete source target (clampedSeedNat seed) N P ell terminalFactor
          T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg draw))
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J) S rootQ).1
    have hleft := (le_max_left _ _).trans h
    simpa only [finalProgramValue, ha, Rat.cast_one, div_one, physicalSource, physicalSourceInterval,
      sourceIntervalAt, substring, List.take_length, List.drop_zero] using hleft
  have hmoment (seed : Seed) (hg : good seed) :
      (∫ draw, max (value seed draw - stateEditCost source target rootQ) 0
        ∂localFinalProgramDrawLaw (R := R) source target N P T H seed) ≤
        (stateEditCost source target rootQ : ℝ) / ell := by
    let project := physicalLocalProgramToComplete (R := R) source target (clampedSeedNat seed)
      N P ell terminalFactor T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg
    let fullValue := finalProgramValue (M := M) (J := J) (R := R) source target N P T S H rootQ seed
    have hpoint (draw : LocalFinalProgramDraw (R := R) source target N P T H seed) :
        value seed draw = fullValue (project draw) :=
      localFinalProgramValue_eq source target N P T S H rootQ seed draw hsize hP hg
    have hmap : (localFinalProgramDrawLaw (R := R) source target N P T H seed).map project =
        finalProgramDrawLaw (R := R) source target N P T H seed :=
      physicalLocalProgramDrawLaw_map source target (clampedSeedNat seed) N P ell terminalFactor
        T thetaExponent H (ell ^ 80) tau hsize hP hF hA hg
    have hcomp := integral_map (μ := localFinalProgramDrawLaw (R := R) source target N P T H seed)
      (φ := project) (measurable_of_finite _).aemeasurable
      (f := fun draw => max (fullValue draw - stateEditCost source target rootQ) 0)
      (measurable_of_finite _).aestronglyMeasurable
    have hfull := physicalProgram_expected_root_excess (R := R) source target N hN hell hMeq hJeq
      (clampedSeedNat seed) P hPeq terminalFactor hA hAupper hsize hg T S hTeq hSeq hHeq bernstein rootQ
    calc
      (∫ draw, max (value seed draw - stateEditCost source target rootQ) 0
          ∂localFinalProgramDrawLaw (R := R) source target N P T H seed) =
          ∫ draw, max (fullValue (project draw) - stateEditCost source target rootQ) 0
            ∂localFinalProgramDrawLaw (R := R) source target N P T H seed := by
        apply integral_congr_ae
        filter_upwards [] with draw
        rw [hpoint]
      _ = ∫ draw, max (fullValue draw - stateEditCost source target rootQ) 0
          ∂finalProgramDrawLaw (R := R) source target N P T H seed := by rw [← hcomp, hmap]
      _ ≤ (stateEditCost source target rootQ : ℝ) / ell := by
        simpa only [fullValue, finalProgramValue, finalProgramDrawLaw, one_div_mul_eq_div] using hfull
  have hDN : stateEditCost source target rootQ ≤ N := by
    have h := physical_state_cost_le (M := M) (J := J) source target N hsize
      ((Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J), rootQ)
    simpa only [physicalSource, physicalSourceInterval, sourceIntervalAt, substring,
      List.take_length, List.drop_zero] using h
  have h := freshSeed_answer_accuracy (localFinalProgramDrawLaw (R := R) source target N P T H)
    terminalLaw good value hDN hD hEll hepsilon haccuracy hseed hlower hmoment
  simpa only [localFinalProgramLaw, localFinalProgramAnswer, heq, ite_false, if_false, terminalLaw, value] using h

end Final

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.localFinalProgram_accuracy_oai.{u_1} := @OAI.EditApproximation.localFinalProgram_accuracy_oai.{u_1}
