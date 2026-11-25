-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.equiv_of_stability
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:50.547383+00:00
-- url     : https://prove2.me/submissions/af7c3a6a-c1b0-4079-a340-2e8841ec443e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorDualCrys_of
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_wachMonoidal_iff
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_unitSumTensorDual_of_wachMonoidal

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
    UnitDualParts.UnitSumTensorDual l P AI H F ↔ TensorLatticeUnitPart.WachMonoidal l P AI H F :=
  ⟨fun h => (wachMonoidal_iff l P AI H F).mpr ⟨h, tensorDualCrys_of l P hT hD⟩,
    unitSumTensorDual_of_wachMonoidal l P AI H F⟩
end GlobalTheory.Cmp.WachMonoidal
