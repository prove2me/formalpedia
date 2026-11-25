-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.wachMonoidal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:51:46.49578+00:00
-- url     : https://prove2.me/submissions/00f5f844-bed6-43f8-a4f6-635cab8bfd9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensor_iff
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_dual_iff
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_sumPart_iff

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
theorem _root_.solution :
    TensorLatticeUnitPart.WachMonoidal l P AI H F ↔ UnitDualParts.UnitSumTensorDual l P AI H F ∧ TensorDualCrys l P := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, (sumPart_iff l P H).mpr h2,
      fun K s LL hg => ((tensor_iff _).mp (h3 K s LL hg)).1,
      fun K s LL hg => ((dual_iff _).mp (h4 K s LL hg)).1⟩,
      fun K s LL hg => ⟨((tensor_iff _).mp (h3 K s LL hg)).2, ((dual_iff _).mp (h4 K s LL hg)).2⟩⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hc⟩
    exact ⟨h1, (sumPart_iff l P H).mp h2,
      fun K s LL hg => (tensor_iff _).mpr ⟨h3 K s LL hg, (hc K s LL hg).1⟩,
      fun K s LL hg => (dual_iff _).mpr ⟨h4 K s LL hg, (hc K s LL hg).2⟩⟩
end GlobalTheory.Cmp.WachMonoidal
