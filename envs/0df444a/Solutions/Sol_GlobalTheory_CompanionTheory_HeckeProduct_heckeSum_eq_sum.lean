-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.heckeSum_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:27.994476+00:00
-- url     : https://prove2.me/submissions/912ba317-8a6c-469b-b5bc-fa0cddd6ec03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_term_support_subset

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
    heckeSum π K f u = ∑ q ∈ hf.toFinset, f q.out • π q.out u :=
  finsum_eq_sum_of_support_subset _ (term_support_subset π K hf u)
end GlobalTheory.CompanionTheory.HeckeProduct
