-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation.SplitRepresentatives.cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:58.045731+00:00
-- url     : https://prove2.me/submissions/577425b4-f92a-4e50-be85-1c08ee44c6ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
namespace SplitRepresentatives
theorem _root_.solution (H : SplitRepresentatives) : SplitRepresentativesCM :=
  fun F E _ _ _ _ _ _ _ => H F E
end SplitRepresentatives
end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
