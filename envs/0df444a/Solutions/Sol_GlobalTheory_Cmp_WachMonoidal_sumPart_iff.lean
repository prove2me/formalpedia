-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.sumPart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:42:42.093778+00:00
-- url     : https://prove2.me/submissions/9554d4d3-f309-4c1c-b12a-d36a33f9897d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_sum_iff

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
theorem _root_.solution : UnitDualParts.SumPart l P H ↔ TensorLatticeUnitPart.SumPart l P H :=
  ⟨fun h K s LL hg => sum_iff.mp (h K s LL hg), fun h K s LL hg => sum_iff.mpr (h K s LL hg)⟩
end GlobalTheory.Cmp.WachMonoidal
