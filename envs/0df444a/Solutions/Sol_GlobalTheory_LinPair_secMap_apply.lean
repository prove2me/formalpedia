-- Prove2me | solution 1 for GlobalTheory.LinPair.secMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:35:46.510301+00:00
-- url     : https://prove2.me/submissions/349d8f7e-ee58-4f5d-a5e7-47029aebac36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SecMapApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.WeilM
open scoped Matrix
open GlobalTheory GlobalTheory.LinPair
variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k]
variable {G H Y : Type} [Group G] [Group H]
namespace GlobalTheory.LinPair
theorem _root_.solution (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) (h : H) :
    secMap om l φ h = l (om (1, h) φ) := rfl
end GlobalTheory.LinPair
