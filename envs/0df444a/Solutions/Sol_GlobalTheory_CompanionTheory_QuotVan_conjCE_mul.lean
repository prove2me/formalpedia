-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.conjCE_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:08.910801+00:00
-- url     : https://prove2.me/submissions/d3e1a874-cf2c-4be7-b1d9-ce7e80fa84e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_conjCE_coe

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
theorem _root_.solution (N : Subgroup Q) [N.Normal] (g h : Q) :
    conjCE N (g * h) = (conjCE N h).trans (conjCE N g) := by
  ext u
  simp [conjCE_coe, mul_assoc]
end GlobalTheory.CompanionTheory.QuotVan
