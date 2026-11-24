-- Prove2me | solution 1 for GlobalTheory.DI.forms_gen_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:19.858031+00:00
-- url     : https://prove2.me/submissions/6ecd818b-dcb0-458c-9c01-ea01e15ca53f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace GlobalTheory.DI
theorem _root_.solution {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩
end GlobalTheory.DI
