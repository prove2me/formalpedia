-- Prove2me | solution 1 for GlobalTheory.WeilM.splitOm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:23.64436+00:00
-- url     : https://prove2.me/submissions/f4c668d7-22a8-497a-8110-f5ab32271516

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
omit [DecidableEq α] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β)
    (h : UG (swapA R) J) (φ : (κ → R) → ℂ) (u : κ → R) :
    splitOm m χ J σ h φ u = splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) *
      φ (flat σ ((flat σ).symm u * ((ugFst J h)⁻¹).valᵀ)) := rfl
end GlobalTheory.WeilM
