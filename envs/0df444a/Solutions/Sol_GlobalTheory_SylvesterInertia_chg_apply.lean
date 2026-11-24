-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.chg_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:45.980983+00:00
-- url     : https://prove2.me/submissions/bbd752d7-bf42-452b-a1d6-e304c3a39b72

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester

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
theorem _root_.solution {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := rfl
end GlobalTheory.SylvesterInertia
