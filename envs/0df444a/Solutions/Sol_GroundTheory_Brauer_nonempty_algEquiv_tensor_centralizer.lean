-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_tensor_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:04.617252+00:00
-- url     : https://prove2.me/submissions/e690b5f7-502e-41de-9681-6ff8a3e9e13e

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer

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
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]
variable [Algebra.IsCentral K B]
namespace GroundTheory.Brauer
theorem _root_.solution :
    Nonempty (A ≃ₐ[K] B ⊗[K] Subalgebra.centralizer K (B : Set A)) :=
  ⟨(tensorCentralizerAlgEquiv B).symm⟩
end GroundTheory.Brauer
