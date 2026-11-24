-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.isUpper_rev_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:30.59565+00:00
-- url     : https://prove2.me/submissions/951a3613-46f2-4479-8391-26874b57f8b1

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_wt_le


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
theorem _root_.solution {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega
end GlobalTheory.CompanionTheory.Iwahori
