-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:35.617205+00:00
-- url     : https://prove2.me/submissions/02fb63b0-bedf-439b-aa93-0bbd1093f11a

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
theorem _root_.solution {L : Type*} [Field L] [Algebra K L] {E : Type*}
    [Field E] [Algebra K E] (σ : L →ₐ[K] E) {n : ℕ}
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty (E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  let _ : Algebra L E := σ.toRingHom.toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun k ↦ (σ.commutes k).symm
  exact ⟨(baseChangeTower K L E A).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans <|
    (baseChangeMatrix L E L (Fin n)).trans (Algebra.TensorProduct.rid L E E).mapMatrix⟩
end GroundTheory.Brauer
