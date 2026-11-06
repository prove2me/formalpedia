-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.rayPhase_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:18.364557+00:00
-- url     : https://prove2.me/submissions/76ec44c6-01f4-478c-9c8b-8f8a1018f518

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
private theorem rayPhaseBits_mul_right
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a (b+c) = rayPhaseBits a b * rayPhaseBits a c := by
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
    (hy : ¬ (2 : O) ∣ y) (hz : ¬ (2 : O) ∣ z) :
    rayPhase x (y*z) = rayPhase x y * rayPhase x z := by
  unfold rayPhase
  rw [rayBits_mul y z hy hz]
  exact rayPhaseBits_mul_right _ _ _
end OAI.ActualEisensteinCoordinates
