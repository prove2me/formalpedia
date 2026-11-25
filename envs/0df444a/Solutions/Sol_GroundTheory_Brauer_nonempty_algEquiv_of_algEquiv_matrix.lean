-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_of_algEquiv_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:26.30735+00:00
-- url     : https://prove2.me/submissions/624dec40-5c4c-442a-b2f8-b7e142eaad78

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Theorems.Thm_GroundTheory_Brauer_exists_isSimpleModule_algEquiv_end

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution {D : Type w} [DivisionRing D] [Algebra K D]
    {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (e : Matrix ι ι D ≃ₐ[K] Matrix ι' ι' D') : Nonempty (D ≃ₐ[K] D') := by
  obtain ⟨I, hI, ⟨φ⟩⟩ := exists_isSimpleModule_algEquiv_end (AlgEquiv.refl : Matrix ι ι D ≃ₐ[K] _)
  obtain ⟨J, hJ, ⟨ψ⟩⟩ := exists_isSimpleModule_algEquiv_end e
  obtain ⟨g⟩ := IsSimpleRing.isIsotypic (Matrix ι ι D) (Matrix ι ι D) I J
  exact ⟨AlgEquiv.op.symm (φ.symm.trans ((g.conjAlgEquiv K).symm.trans ψ))⟩
end GroundTheory.Brauer
