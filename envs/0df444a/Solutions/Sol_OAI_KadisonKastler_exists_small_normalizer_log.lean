-- Prove2me | solution 1 for OAI.KadisonKastler.exists_small_normalizer_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:15.630851+00:00
-- url     : https://prove2.me/submissions/265c7680-237d-4f28-a3bf-90651fb19acf

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K012
import Theorems.Thm_OAI_KadisonKastler_commutator_mem_of_small_expUnitary_normalizes

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryLogarithmBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A controlled self-adjoint logarithm near the identity -/

namespace KadisonKastler

open scoped Real

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_argSelfAdjoint_le_two_mul (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ‖Unitary.argSelfAdjoint u‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ := by
  let θ := ‖Unitary.argSelfAdjoint u‖
  let d := ‖(u : H →L[ℂ] H) - 1‖
  have hθ : 0 ≤ θ := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hθpi : θ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi u
  have hc := Real.cos_le_one_sub_mul_cos_sq
    (x := θ) (by rwa [abs_of_nonneg hθ])
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hc' : Real.pi ^ 2 * Real.cos θ ≤ Real.pi ^ 2 - 2 * θ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hc hpi.le
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have heq : 2 * (1 - Real.cos θ) = d ^ 2 :=
    Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint hu
  have heq' := congrArg (fun r : ℝ => Real.pi ^ 2 * r) heq
  have hb : 4 * θ ^ 2 ≤ Real.pi ^ 2 * d ^ 2 := by nlinarith
  have hpi4 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hb' := mul_le_mul_of_nonneg_right hpi4 (sq_nonneg d)
  change θ ≤ 2 * d
  nlinarith

theorem exists_small_selfAdjoint_log (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = u ∧
      ‖h‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ :=
  ⟨Unitary.argSelfAdjoint u, expUnitary_argSelfAdjoint hu,
    norm_argSelfAdjoint_le_two_mul u hu⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerLogarithm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The logarithm of a small normalizer preserves the algebra

The bounded operators preserving a closed linear subspace form a closed
subalgebra. Uniform exponential inversion recovers the commutator generator
inside that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The controlled principal logarithm of a sufficiently small exact
normalizer implements a derivation of the algebra. -/
theorem exists_small_normalizer_log_oai (P : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates (H := H) v P P)
    (hsmall : ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64) :
    ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = v ∧
      ‖(h : H →L[ℂ] H)‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ ∧
      ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P := by
  obtain ⟨h, hh, hn⟩ := exists_small_selfAdjoint_log v (by linarith)
  refine ⟨h, hh, hn, ?_⟩
  apply commutator_mem_of_small_expUnitary_normalizes P h
  · exact hn.trans (by linarith)
  · rwa [hh]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_small_normalizer_log_oai.{u_1} := @OAI.KadisonKastler.exists_small_normalizer_log_oai.{u_1}
