-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.stable_iff_exists_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:45.193331+00:00
-- url     : https://prove2.me/submissions/49482fd2-72f3-4724-b67e-cb99e947270e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
import Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_rationalPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (W : Submodule L (L ⊗[K] V)) :
    (∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange L = W := by
  constructor
  · intro hW
    refine ⟨_, baseChange_rationalPart s hs W hW, fun N hN => ?_⟩
    rw [← hN, rationalPart_baseChange]
  · rintro ⟨N, rfl, -⟩ g _ ⟨t, rfl⟩
    exact ⟨(s g).toLinearMap.rTensor N t, (LinearMap.rTensor_baseChange (s g) t N.subtype).symm⟩
end GlobalTheory.GaloisDescent
