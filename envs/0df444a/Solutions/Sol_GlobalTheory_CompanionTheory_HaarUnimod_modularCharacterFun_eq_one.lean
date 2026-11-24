-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarUnimod.modularCharacterFun_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:42.608103+00:00
-- url     : https://prove2.me/submissions/02d3d13e-3968-4d82-8640-d6672015e56f

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarUnimod
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
namespace GlobalTheory.CompanionTheory.HaarUnimod
theorem _root_.solution (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g
end GlobalTheory.CompanionTheory.HaarUnimod
