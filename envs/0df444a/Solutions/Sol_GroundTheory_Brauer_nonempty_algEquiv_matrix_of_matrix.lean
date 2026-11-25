-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_matrix_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:37.240786+00:00
-- url     : https://prove2.me/submissions/edd449ca-685b-4b69-9ede-1055edc2ac3e

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting

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
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
namespace GroundTheory.Brauer
theorem _root_.solution {L : Type*} [Field L] [Algebra K L] {D : Type*}
    [Ring D] [Algebra K D] {m k : ℕ} (eA : A ≃ₐ[K] Matrix (Fin m) (Fin m) D)
    (eD : L ⊗[K] D ≃ₐ[L] Matrix (Fin k) (Fin k) L) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (m * k)) (Fin (m * k)) L) :=
  ⟨(Algebra.TensorProduct.congr AlgEquiv.refl eA).trans <|
    (baseChangeMatrix K L D (Fin m)).trans <| eD.mapMatrix.trans <|
      (Matrix.compAlgEquiv (Fin m) (Fin k) L L).trans
        (Matrix.reindexAlgEquiv L L finProdFinEquiv)⟩
end GroundTheory.Brauer
