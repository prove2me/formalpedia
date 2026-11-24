-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isCompact_intS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:18.716648+00:00
-- url     : https://prove2.me/submissions/42f99605-1a0e-4240-8294-d7225872f4f5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_mem_intS
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isCompact_box
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_UpperTheory_Reformulated_B_Qf31_isCompact_box
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
variable [ProperSpace L]
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution : IsCompact ((intS : Subgroup (GL (Fin m) L)) : Set (GL (Fin m) L)) := by
  convert isCompact_box (L := L) (m := m) 0 1 using 1
  ext g
  simp [mem_intS, IsInt]
end GlobalTheory.CompanionTheory.BLevel
