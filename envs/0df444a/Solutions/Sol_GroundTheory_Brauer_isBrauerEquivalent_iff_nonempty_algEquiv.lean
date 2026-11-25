-- Prove2me | solution 1 for GroundTheory.Brauer.isBrauerEquivalent_iff_nonempty_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:31.923805+00:00
-- url     : https://prove2.me/submissions/2d3394d6-95f4-4912-885d-d89d91ae5cf6

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_algEquiv_matrix

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
theorem _root_.solution {A B : CSA.{u, v} K} {D : Type w}
    [DivisionRing D] [Algebra K D] {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (eA : A ≃ₐ[K] Matrix ι ι D) (eB : B ≃ₐ[K] Matrix ι' ι' D') :
    IsBrauerEquivalent A B ↔ Nonempty (D ≃ₐ[K] D') := by
  constructor
  · rintro ⟨n, m, hn, hm, ⟨f⟩⟩
    have : NeZero n := ⟨hn⟩
    have : NeZero m := ⟨hm⟩
    exact nonempty_algEquiv_of_algEquiv_matrix <|
      (Matrix.compAlgEquiv (Fin n) ι D K).symm.trans <| eA.symm.mapMatrix.trans <| f.trans <|
        eB.mapMatrix.trans <| Matrix.compAlgEquiv (Fin m) ι' D' K
  · rintro ⟨g⟩
    exact isBrauerEquivalent_of_algEquiv_matrix eA (eB.trans g.symm.mapMatrix)
end GroundTheory.Brauer
