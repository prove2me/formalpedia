-- Prove2me | solution 1 for GlobalTheory.WeilM.isSplitting_splitOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:01.361798+00:00
-- url     : https://prove2.me/submissions/a17cdf2f-bf0c-4b5d-91ff-0ebf5012cbe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_splitOm_rho
import Theorems.Thm_GlobalTheory_WeilM_splitOm_mem_SB

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
theorem _root_.solution [Invertible (2 : R)] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ) :
    IsSplitting (sbClass R) ψ (splitDarboux hA hB σ) (actB (swapA R)) (splitOm m χ JB σ) where
  pres g _ hφ := splitOm_mem_SB m χ JB σ g hφ
  impl g w φ _ := splitOm_rho m χ hA hB σ ψ g w φ
  adm _ _ _ := Set.mem_univ _
end GlobalTheory.WeilM
