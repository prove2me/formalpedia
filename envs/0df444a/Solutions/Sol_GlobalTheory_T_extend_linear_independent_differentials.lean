-- Prove2me | solution 1 for GlobalTheory.T.extend_linear_independent_differentials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:00.943785+00:00
-- url     : https://prove2.me/submissions/81767621-bc7c-4d6d-80fa-86ca9080cc33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendLinearIndependentDifferentials
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendLinearIndependentDifferentialsStatement
import Theorems.Thm_GlobalTheory_kaehler_baseChange_independent_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B), Module.finrank K (K ⊗[B] Ω[B⁄R]) = d → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) → ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧ LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  first | exact @GlobalTheory.kaehler_baseChange_independent_extend | exact GlobalTheory.kaehler_baseChange_independent_extend | (intros; apply GlobalTheory.kaehler_baseChange_independent_extend <;> assumption)
end _root_.GlobalTheory.T
