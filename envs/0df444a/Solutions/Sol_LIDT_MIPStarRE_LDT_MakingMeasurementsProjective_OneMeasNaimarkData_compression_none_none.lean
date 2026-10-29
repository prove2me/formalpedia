-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.OneMeasNaimarkData.compression_none_none
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:06:22.735528+00:00
-- url     : https://prove2.me/submissions/0d7a20de-07d2-4fa6-8e00-e129aee1c8e2

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.OneMeasNaimarkData.compression_none_none.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkOneMeas
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 5 — Naimark tensor-product assembly

Questionwise one-measurement Naimark data, the two-sided trace identity, and
the source-facing tensor-product Naimark theorem in the projective-submeasurement
form supplied by the paper's helper lemma.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u



/-! ### Questionwise Naimark dilation interface -/







/-! ### Full tensor-product Naimark interface -/

theorem solution
    {Outcome : Type u} [Fintype Outcome] [DecidableEq Outcome]
    {d : Type u} [Fintype d] [DecidableEq d]
    (data : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.OneMeasNaimarkData Outcome d) (a : Outcome) (i j : d) :
    data.liftedEffect (some a) (i, none) (j, none) =
      data.source.effect a i j := by
  classical
  let : Nonempty d := ⟨i⟩
  have h := data.expectation_preservation (Matrix.single j i (1 : ℂ)) a
  unfold _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity _root_.LIDT.MIPStarRE.Quantum.normalizedTrace at h
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector,
    Matrix.single, Fintype.sum_prod_type] at h
  have hd : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hOutcome : (Fintype.card (Option Outcome) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hd, hOutcome] at h
  have hsum_if_pair_eq :
      ∀ F : d → d → ℂ,
        (∑ x : d, ∑ y : d, if j = x ∧ i = y then F y x else 0) = F i j := by
    intro F
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro y _ hyi
        simp [show i ≠ y by exact fun h => hyi h.symm]
      · intro hi
        simp at hi
    · intro x _ hxj
      simp [show j ≠ x by exact fun h => hxj h.symm]
    · intro hj
      simp at hj
  rw [hsum_if_pair_eq (fun y x => data.source.effect a y x)] at h
  rw [← Finset.mul_sum] at h
  rw [hsum_if_pair_eq (fun y x => data.liftedEffect (some a) (y, none) (x, none))] at h
  have hc : (↑(Fintype.card Outcome) + 1 : ℂ) ≠ 0 := by
    positivity
  exact mul_left_cancel₀ hc (by
    calc
      (↑(Fintype.card Outcome) + 1 : ℂ) *
          data.liftedEffect (some a) (i, none) (j, none) =
        data.source.effect a i j * (↑(Fintype.card Outcome) + 1 : ℂ) := h.symm
      _ = (↑(Fintype.card Outcome) + 1 : ℂ) * data.source.effect a i j := by ring)
