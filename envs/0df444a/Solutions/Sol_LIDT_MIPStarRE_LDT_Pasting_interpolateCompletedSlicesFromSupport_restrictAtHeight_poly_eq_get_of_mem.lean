-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:33:33.011617+00:00
-- url     : https://prove2.me/submissions/2c99eefd-7fdd-475e-8b7e-6f13b8390917

-- Generated proof for MIPStarRE.LDT.Pasting.interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Line interpolation: core API

Interpolation-support, vertical-line restriction, and completed-slice
interpolation lemmas from `ld-pasting.tex` that form the foundation for the
line-interpolation estimates.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {k : ℕ} (xs : _root_.LIDT.MIPStarRE.LDT.PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.interpolateCompletedSlicesFromSupport params xs gs σ hσsubset hσcard).poly =
      ((gs i).get (by simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → _root_.LIDT.MIPStarRE.LDT.Scalar params := fun j => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    exact hxs (by simpa [v] using congrArg (_root_.LIDT.MIPStarRE.LDT.encodeScalar (params := params)) hab)
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)) =
        MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)) := by
    simp [_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap, _root_.LIDT.MIPStarRE.LDT.lastCoord]
  unfold _root_.LIDT.MIPStarRE.LDT.Pasting.interpolateCompletedSlicesFromSupport
  simp only
  trans ∑ idx ∈ σ.attach,
      MvPolynomial.eval₂Hom MvPolynomial.C
        (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
        (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
            (Lagrange.basis σ (fun i : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)) idx.1) *
          (MvPolynomial.rename (_root_.LIDT.MIPStarRE.LDT.embedCoord params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs idx.1 (hσsubset idx.2)).poly)
  · exact map_sum
      (g := MvPolynomial.eval₂Hom MvPolynomial.C
        (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i)))
      (s := σ.attach)
      (f := fun idx : {j // j ∈ σ} =>
        _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
            (Lagrange.basis σ (fun i : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)) idx.1) *
          (MvPolynomial.rename (_root_.LIDT.MIPStarRE.LDT.embedCoord params))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs idx.1 (hσsubset idx.2)).poly)
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (_root_.LIDT.MIPStarRE.LDT.embedCoord params) (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs i (hσsubset hi)).poly) =
          (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs i (hσsubset hi)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ _root_.LIDT.MIPStarRE.LDT.embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap, _root_.LIDT.MIPStarRE.LDT.embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i))) = 1 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
              (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
              (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
              (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i))
                            hcomp
          _ = 1 := by
                rw [_root_.Polynomial.eval₂_at_apply]
                have hscalar :
                    _root_.Polynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i))
                      (Lagrange.basis σ (fun j => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i) = 1 := by
                  simpa [v] using Lagrange.eval_basis_self hvinj hi
                change MvPolynomial.C
                    (_root_.Polynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i))
                      (Lagrange.basis σ (fun j => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j)) i)) =
                  (1 : _root_.LIDT.MIPStarRE.LDT.PolynomialModel params)
                rw [hscalar]
                simp
    rw [hLi, hslice]
    simp [_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly]
  · intro j hj hji
    have hji' : j.1 ≠ i := by
      intro hEq
      apply hji
      exact Subtype.ext hEq
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (_root_.LIDT.MIPStarRE.LDT.embedCoord params) (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs j.1 (hσsubset j.2)).poly) =
          (_root_.LIDT.MIPStarRE.LDT.Pasting.extractSlicePoly gs j.1 (hσsubset j.2)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ _root_.LIDT.MIPStarRE.LDT.embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap, _root_.LIDT.MIPStarRE.LDT.embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
            (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1))) = 0 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params))
              (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
              (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
              (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (_root_.LIDT.MIPStarRE.LDT.lastCoord params)))
                      (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1))
                            hcomp
        _ = 0 := by
              have hbasis :
                  (Lagrange.basis σ (fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1).eval
                    (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i)) = 0 := by
                simpa using
                  (Lagrange.eval_basis_of_ne
                    (s := σ) (v := fun j' : Fin k => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j'))
                    (i := j.1) (j := i) hji' hi)
              rw [_root_.Polynomial.eval₂_at_apply]
              have hscalar :
                  _root_.Polynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i))
                    (Lagrange.basis σ (fun j' => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1) = 0 := by
                simpa [v] using hbasis
              change MvPolynomial.C
                  (_root_.Polynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodeScalar (xs i))
                    (Lagrange.basis σ (fun j' => _root_.LIDT.MIPStarRE.LDT.decodeScalar (xs j')) j.1)) =
                (0 : _root_.LIDT.MIPStarRE.LDT.PolynomialModel params)
              rw [hscalar]
              simp
    rw [hLi, hslice]
    simp
  · intro hnot
    exact (hnot (by simp : ((⟨i, hi⟩ : {x // x ∈ σ}) ∈ σ.attach))).elim
