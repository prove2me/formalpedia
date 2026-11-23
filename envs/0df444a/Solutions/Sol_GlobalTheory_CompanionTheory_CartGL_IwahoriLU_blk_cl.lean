-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:54.806866+00:00
-- url     : https://prove2.me/submissions/6e6f53d6-3b8e-412f-9701-08a918605648

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_blk_cc
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

set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
omit [IsUltrametricDist L]
namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU
theorem _root_.solution (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (i : Fin n) :
    blk P b c d i.castSucc (Fin.last n) = b i := by simp [blk]
end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
