-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:07.04426+00:00
-- url     : https://prove2.me/submissions/333e48e0-320c-424c-a664-f689ffa63560

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
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



set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
omit [IsUltrametricDist L]
namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU
theorem _root_.solution (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (i j : Fin n) :
    blk P b c d i.castSucc j.castSucc = P i j := by simp [blk]
end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
