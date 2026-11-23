-- Prove2me | solution 1 for GroundTheory.Brauer.isBrauerEquivalent_of_algEquiv_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:40.457203+00:00
-- url     : https://prove2.me/submissions/cb766a83-152e-48c0-95a7-feb548c16916

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv

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
theorem _root_.solution {A B : CSA.{u, v} K} {C : Type w} [Ring C]
    [Algebra K C] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι']
    [DecidableEq ι'] [Nonempty ι'] (eA : A ≃ₐ[K] Matrix ι ι C) (eB : B ≃ₐ[K] Matrix ι' ι' C) :
    IsBrauerEquivalent A B := by
  refine ⟨Fintype.card ι', Fintype.card ι, Fintype.card_ne_zero, Fintype.card_ne_zero, ⟨?_⟩⟩
  exact (Matrix.reindexAlgEquiv K A (Fintype.equivFin ι').symm).trans <|
    eA.mapMatrix.trans <| (Matrix.compAlgEquiv ι' ι C K).trans <|
    (Matrix.reindexAlgEquiv K C (Equiv.prodComm ι' ι)).trans <|
    (Matrix.compAlgEquiv ι ι' C K).symm.trans <| eB.symm.mapMatrix.trans <|
    Matrix.reindexAlgEquiv K B (Fintype.equivFin ι)
end GroundTheory.Brauer
