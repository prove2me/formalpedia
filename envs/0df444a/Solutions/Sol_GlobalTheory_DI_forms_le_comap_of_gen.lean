-- Prove2me | solution 1 for GlobalTheory.DI.forms_le_comap_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:21.035531+00:00
-- url     : https://prove2.me/submissions/91cd69a1-9b4b-4e80-a723-f148a9fce12a

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
theorem _root_.solution {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv
end GlobalTheory.DI
