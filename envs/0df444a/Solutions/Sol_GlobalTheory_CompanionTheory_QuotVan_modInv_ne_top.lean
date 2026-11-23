-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.modInv_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:19.737253+00:00
-- url     : https://prove2.me/submissions/9675acb0-2b9f-4cf0-8cee-fd117c3a2fc8

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
variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution (m : M) : modInv N M m ≠ ∞ := by
  have h := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  simp [modInv, h]
end GlobalTheory.CompanionTheory.QuotVan
