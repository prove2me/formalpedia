-- Prove2me | solution 1 for GlobalTheory.Hadamard.det_gram_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:23.334871+00:00
-- url     : https://prove2.me/submissions/03403792-aaea-4e57-8982-a0bd45372e32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι]
namespace GlobalTheory.Hadamard
theorem _root_.solution [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det :=
  det_submatrix_equiv_self σ (gram 𝕜 x)
end GlobalTheory.Hadamard
