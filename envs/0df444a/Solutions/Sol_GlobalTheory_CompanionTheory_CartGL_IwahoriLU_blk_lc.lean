-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:40.136372+00:00
-- url     : https://prove2.me/submissions/123e7563-e9d2-422f-8b9d-507c5fe6fb85

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_blk_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_blk_cl
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


attribute [local simp] GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cc
attribute [local simp] GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cl

set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
omit [IsUltrametricDist L]
namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU
theorem _root_.solution (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (j : Fin n) :
    blk P b c d (Fin.last n) j.castSucc = c j := by simp [blk]
end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
