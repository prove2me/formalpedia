-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isClosed_UG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:30.370201+00:00
-- url     : https://prove2.me/submissions/e58480ad-1840-4e1d-ae20-22396ff4c402

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
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {L : Type} [NontriviallyNormedField L] (s : L →+* L) (hs : ∀ x, ‖s x‖ = ‖x‖) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) : IsClosed (UG s J : Set (GL (Fin n) L)) := by
  have hc : Continuous s := (AddMonoidHomClass.isometry_of_norm s hs).continuous
  have e : (UG s J : Set (GL (Fin n) L)) = {g | (g.1.map s).transpose * J * g.1 = J} := rfl
  rw [e]
  exact isClosed_eq (((Units.continuous_val.matrix_map hc).matrix_transpose.matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const
end GlobalTheory.CompanionTheory.BLevel
