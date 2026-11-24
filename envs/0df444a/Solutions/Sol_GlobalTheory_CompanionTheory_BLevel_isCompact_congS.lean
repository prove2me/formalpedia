-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isCompact_congS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:31.107805+00:00
-- url     : https://prove2.me/submissions/5a630e74-9331-4581-b994-a6be8ab8070b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isCompact_box
import Theorems.Thm_UpperTheory_Reformulated_B_Qf31_isCompact_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
variable [ProperSpace L]
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : IsCompact ((congS r h0 h1 : Subgroup (GL (Fin m) L)) : Set (GL (Fin m) L)) := by
  convert isCompact_box (L := L) (m := m) 1 r using 1
  ext g
  constructor
  · intro hg
    exact ⟨hg, (congS r h0 h1).inv_mem hg⟩
  · intro hg
    exact hg.1
end GlobalTheory.CompanionTheory.BLevel
