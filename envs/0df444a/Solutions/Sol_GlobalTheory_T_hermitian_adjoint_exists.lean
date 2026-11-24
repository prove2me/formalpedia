-- Prove2me | solution 1 for GlobalTheory.T.hermitian_adjoint_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:22.379009+00:00
-- url     : https://prove2.me/submissions/baeb89fb-d879-4092-ad71-02382ea61438

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExists
import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_exists_adjoint_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h → ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | exact GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | (intros; apply GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm <;> assumption)
end _root_.GlobalTheory.T
