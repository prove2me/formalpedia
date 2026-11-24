-- Prove2me | solution 1 for GlobalTheory.pairQuadraticForm_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:20.648271+00:00
-- url     : https://prove2.me/submissions/6dead321-b44b-4dce-b8f8-f4838a6e184d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    pairQuadraticForm hd hs he (Submodule.Quotient.mk ν) =
      ((((fun i => (ν i : ℚ)) ⬝ᵥ (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ
        fun i => (ν i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl
end GlobalTheory
