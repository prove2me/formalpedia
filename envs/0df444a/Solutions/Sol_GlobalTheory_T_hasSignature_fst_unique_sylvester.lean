-- Prove2me | solution 1 for GlobalTheory.T.hasSignature_fst_unique_sylvester
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:14.441037+00:00
-- url     : https://prove2.me/submissions/490acc8e-b7e9-4d66-a328-436fb8421376

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvesterStatement
import Theorems.Thm_GlobalTheory_SylvesterInertia_hasSignature_fst_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  first | exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique | exact GlobalTheory.SylvesterInertia.hasSignature_fst_unique | (intros; apply GlobalTheory.SylvesterInertia.hasSignature_fst_unique <;> assumption)
end _root_.GlobalTheory.T
