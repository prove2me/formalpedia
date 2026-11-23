-- Prove2me | solution 1 for GlobalTheory.mem_monomialExponents
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:17.206877+00:00
-- url     : https://prove2.me/submissions/fee5cfc4-0a06-4b76-9463-943a0514630a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := Iff.rfl
end GlobalTheory
