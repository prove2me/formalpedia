-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.out_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:42.827804+00:00
-- url     : https://prove2.me/submissions/ba5b3f2e-3254-4e0f-93a3-1e50427f64b8

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
namespace GlobalTheory.CompanionTheory.HeckeProduct
theorem _root_.solution (K : Subgroup G) (F : G → M) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (g : G) :
    F ((g : G ⧸ K).out) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hh]; exact hF g h h.2
end GlobalTheory.CompanionTheory.HeckeProduct
