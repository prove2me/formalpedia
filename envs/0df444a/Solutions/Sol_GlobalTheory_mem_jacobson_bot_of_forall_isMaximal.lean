-- Prove2me | solution 1 for GlobalTheory.mem_jacobson_bot_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:22.330803+00:00
-- url     : https://prove2.me/submissions/560e30ab-ab17-41a5-9403-947a168f20c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] {x : S}
    (h : ∀ n : Ideal S, n.IsMaximal → x ∈ n) : x ∈ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro n ⟨-, hn⟩
  exact h n hn
end GlobalTheory
