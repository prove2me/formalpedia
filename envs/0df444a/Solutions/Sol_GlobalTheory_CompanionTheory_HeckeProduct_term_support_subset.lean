-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.term_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:37.995115+00:00
-- url     : https://prove2.me/submissions/4479c112-d813-4e93-8f6b-0f518b16a67e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple

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
    (Function.support fun q : G ⧸ K => f q.out • π q.out u) ⊆ hf.toFinset := by
  intro q hq
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro h0
  exact hq (by simp [h0])
end GlobalTheory.CompanionTheory.HeckeProduct
