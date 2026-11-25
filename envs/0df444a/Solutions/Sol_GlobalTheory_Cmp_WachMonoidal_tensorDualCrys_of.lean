-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.tensorDualCrys_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:45.43158+00:00
-- url     : https://prove2.me/submissions/ca2e10d8-fe4b-4cf3-80c8-39ad68f562c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorLatCrys_of
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_dualLatCrys_of
import Theorems.Thm_GlobalTheory_Per_integers_completeDVR


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
theorem _root_.solution (hT : CrystallineSubrepresentation.LocTensorCrys l P) (hD : CrystallineSubrepresentation.LocDualCrys l P) :
    TensorDualCrys l P := fun K _ LL _ => by
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  exact ⟨tensorLatCrys_of (hT K LL), dualLatCrys_of (hD K LL)⟩
end GlobalTheory.Cmp.WachMonoidal
