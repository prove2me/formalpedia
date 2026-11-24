-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.normal_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:26.456865+00:00
-- url     : https://prove2.me/submissions/cbb5d884-87ab-49f7-b399-11963a8e7ed6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (z : PrimeSpectrum A) : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk z) :=
  isIntegrallyClosed_of_isLocalization _ z.asIdeal.primeCompl
    z.asIdeal.primeCompl_le_nonZeroDivisors
end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
