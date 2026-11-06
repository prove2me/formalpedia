-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:42.967206+00:00
-- url     : https://prove2.me/submissions/d3f34f0f-3df7-451a-9ff2-e2f6604c0df9

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
theorem _root_.solution (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring
end OAI.ActualEisensteinCoordinates
