-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.conjCE_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:42.627881+00:00
-- url     : https://prove2.me/submissions/430932ea-cd03-4376-b511-ead3a6cfb986

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution (N : Subgroup Q) [N.Normal] (g : Q) (u : N) :
    ((conjCE N g u : N) : Q) = g * u * g⁻¹ := rfl
end GlobalTheory.CompanionTheory.QuotVan
