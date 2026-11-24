-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.hasSignature_fst_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:30.957745+00:00
-- url     : https://prove2.me/submissions/2b07c79e-7acf-45a1-a5b3-d8bb5333e1af

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
import Theorems.Thm_GlobalTheory_SylvesterInertia_fst_le_of_hasSignature

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SylvesterInertia
theorem _root_.solution : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ},
    Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' :=
  fun h h' => le_antisymm (fst_le_of_hasSignature h h') (fst_le_of_hasSignature h' h)
end GlobalTheory.SylvesterInertia
