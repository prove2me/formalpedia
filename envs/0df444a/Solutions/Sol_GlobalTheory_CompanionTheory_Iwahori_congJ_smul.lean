-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.congJ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:30.250714+00:00
-- url     : https://prove2.me/submissions/f67a978a-6087-479d-8e0c-fef77b3f8b44

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorizationStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLowerStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruenceStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpperStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_lat_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori
namespace GlobalTheory.CompanionTheory.Iwahori
theorem _root_.solution {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]
end GlobalTheory.CompanionTheory.Iwahori
