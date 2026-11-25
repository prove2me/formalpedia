-- Prove2me | solution 1 for GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:07:48.275811+00:00
-- url     : https://prove2.me/submissions/0eb759e9-cd3d-4cf1-8441-81c90602c143

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_PointRingCommRing
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LocalRingStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeightsFromJumpsIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeightsFromJumpsCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
open TensorProduct
namespace GlobalTheory.HeightsFromJumpsCompare
namespace _root_.GlobalTheory.HeightsFromJumpsCompare
theorem _root_.solution (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C :=
  Iff.rfl
end _root_.GlobalTheory.HeightsFromJumpsCompare
end GlobalTheory.HeightsFromJumpsCompare
