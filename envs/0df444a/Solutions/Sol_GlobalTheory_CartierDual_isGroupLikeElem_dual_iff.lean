-- Prove2me | solution 1 for GlobalTheory.CartierDual.isGroupLikeElem_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:43.069695+00:00
-- url     : https://prove2.me/submissions/25536940-401e-4a4a-8f69-5f673e814791

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_CartierDual_comul_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open GlobalTheory.CartierDual
namespace GlobalTheory.CartierDual
theorem _root_.solution {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H]
    [Module.Finite R H] [Module.Projective R H] (φ : CartierDual R H) :
    IsGroupLikeElem R φ ↔ φ 1 = 1 ∧ ∀ a b, φ (a * b) = φ a * φ b := by
  rw [isGroupLikeElem_iff, comul_eq_iff]
  simp [eq_comm]
end GlobalTheory.CartierDual
