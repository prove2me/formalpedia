-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:18.796256+00:00
-- url     : https://prove2.me/submissions/4bd939e9-a681-430d-bff6-0733ac243a0f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
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
theorem _root_.solution (c : Matrix (Fin m) (Fin m) L) (r : ℝ) :
    IsCompact {g : GL (Fin m) L | (∀ i j, ‖g.1 i j - c i j‖ ≤ r) ∧ ∀ i j, ‖(g⁻¹).1 i j - c i j‖ ≤ r} :=
  _root_.UpperTheory.Reformulated.B.Qf31.isCompact_box c r
end GlobalTheory.CompanionTheory.BLevel
