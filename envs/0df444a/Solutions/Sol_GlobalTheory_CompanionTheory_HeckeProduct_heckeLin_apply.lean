-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.heckeLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:37:03.118801+00:00
-- url     : https://prove2.me/submissions/46993bd7-49ae-40a8-93f2-7ca7cfe326d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_heckeSum_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
variable {G M V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ G V) (K : Subgroup G) {f : G → ℂ}
namespace GlobalTheory.CompanionTheory.HeckeProduct
theorem _root_.solution (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeLin π K hf u = heckeSum π K f u := by
  rw [heckeSum_eq_sum π K hf, heckeLin, LinearMap.sum_apply]
  rfl
end GlobalTheory.CompanionTheory.HeckeProduct
