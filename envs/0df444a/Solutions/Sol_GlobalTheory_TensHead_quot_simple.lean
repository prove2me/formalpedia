-- Prove2me | solution 1 for GlobalTheory.TensHead.quot_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:40.458084+00:00
-- url     : https://prove2.me/submissions/f45529b2-3ae9-40e4-b8c5-303973733594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) (hs : Stab G K) (hK : SimpleOver G K) :
    ∀ U : Submodule ℂ (V ⧸ K), Stab (quotOps G K) U → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hst : Stab G (U.comap K.mkQ) := by
    intro g hg x hx
    have hf : (K.mapQ K g (fun y hy => hs g hg y hy)) ∘ₗ K.mkQ = K.mkQ ∘ₗ g := by
      ext y; simp
    have := hU _ ⟨g, hg, hf⟩ _ hx
    simpa using this
  have hle : K ≤ U.comap K.mkQ := by
    intro x hx; simp [(Submodule.Quotient.mk_eq_zero K).2 hx]
  rcases hK _ hst hle with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.mkQ_map_self]
  · right
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.map_top,
      LinearMap.range_eq_top.2 K.mkQ_surjective]
end GlobalTheory.TensHead
