-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.congS_le_intS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:28.914135+00:00
-- url     : https://prove2.me/submissions/da8cb8e8-fb10-4d29-abc0-870c6dbdffc9

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact

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
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : congS (L := L) (m := m) r h0 h1 ≤ intS := fun g hg =>
  ⟨IsNear.isInt h1.le hg, IsNear.isInt h1.le ((congS r h0 h1).inv_mem hg)⟩
end GlobalTheory.CompanionTheory.BLevel
