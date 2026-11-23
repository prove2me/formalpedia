-- Prove2me | solution 1 for GlobalTheory.WeilM.splitDarboux_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:43.06482+00:00
-- url     : https://prove2.me/submissions/25c2a711-fcdc-4d2d-a05c-ad65519432b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (x : Matrix α β (R × R)) :
    (splitDarboux hA hB σ).e x = (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ)) := rfl
end GlobalTheory.WeilM
