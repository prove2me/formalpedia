-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.rayPhase_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:17.70954+00:00
-- url     : https://prove2.me/submissions/21c203b8-42e2-4c6c-8fc6-928455b0a135

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_rayBits_mul
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
private theorem rayPhaseBits_mul_left
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits (a+b) c = rayPhaseBits a c * rayPhaseBits b c := by
  decide +revert
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
theorem _root_.solution (x y z : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayPhase (x*y) z = rayPhase x z * rayPhase y z := by
  unfold rayPhase
  rw [rayBits_mul x y hx hy]
  exact rayPhaseBits_mul_left _ _ _
end OAI.ActualEisensteinCoordinates
