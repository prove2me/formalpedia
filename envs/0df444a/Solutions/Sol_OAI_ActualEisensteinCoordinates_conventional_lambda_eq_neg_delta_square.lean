-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.conventional_lambda_eq_neg_delta_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:06.104212+00:00
-- url     : https://prove2.me/submissions/22632570-922d-4a65-a4f0-5bcf81861586

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ShortDraftConcretePhase
open ShortDraftTrace
end ShortDraftConcretePhase
namespace ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGauss
namespace EisensteinRayPhase
end EisensteinRayPhase
namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]
end ShortDraftSextic
namespace ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGaussJacobi
namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftQuadraticGauss
namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]
end ShortDraftQuotientPhase
namespace EisensteinEPrimaryPhase
end EisensteinEPrimaryPhase
namespace ShortDraftGaussianPhaseTable
end ShortDraftGaussianPhaseTable
namespace ActualEisensteinCoordinates
private theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ
end ActualEisensteinCoordinates
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinCoordinates
namespace OAI.ActualEisensteinCoordinates
theorem _root_.solution :
    omega - 1 = -eval 1 2 * omega ^ 2 := by
  have hc : omega ^ 3 = 1 := hζ.toInteger_cube_eq_one
  calc
    omega - 1 = -omega ^ 2 - 2 * omega ^ 3 := by
      rw [omega_sq, hc]
      ring
    _ = -eval 1 2 * omega ^ 2 := by
      simp only [eval]
      push_cast
      ring
end OAI.ActualEisensteinCoordinates
