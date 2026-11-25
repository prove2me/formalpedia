-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.unitSumTensorDual_of_wachMonoidal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:43.947509+00:00
-- url     : https://prove2.me/submissions/c71819fc-e74c-4cb3-bf26-2ad68a897b58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_wachMonoidal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution (h : TensorLatticeUnitPart.WachMonoidal l P AI H F) :
    UnitDualParts.UnitSumTensorDual l P AI H F :=
  ((wachMonoidal_iff l P AI H F).mp h).1
end GlobalTheory.Cmp.WachMonoidal
